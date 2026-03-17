// Lean compiler output
// Module: Lean.Elab.Tactic.Rewrite
// Imports: public import Lean.Meta.Tactic.Rewrite public import Lean.Meta.Tactic.Replace public import Lean.Elab.Tactic.Location import Lean.Meta.Eqns
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_abortTacticExceptionId;
lean_object* l_Lean_Elab_Tactic_withMainContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___closed__0 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___closed__1 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__0;
static lean_once_cell_t l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabRewrite___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Occurs check failed: Expression"};
static const lean_object* l_Lean_Elab_Tactic_elabRewrite___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabRewrite___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewrite___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewrite___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_elabRewrite___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "\ncontains the goal "};
static const lean_object* l_Lean_Elab_Tactic_elabRewrite___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_elabRewrite___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewrite___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewrite___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Failed to rewrite using equation theorems for `"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Try rewriting with `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_withRWRulesSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_withRWRulesSeq___lam__1___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_withRWRulesSeq___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value;
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Rewrite"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value;
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Config"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Error evaluating configuration\n"};
static const lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\n\nException: "};
static const lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Configuration contains `sorry`"};
static const lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__5;
static const lean_ctor_object l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "Error evaluating configuration: Environment does not yet contain type "};
static const lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__9;
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 67, 55, 19, 78, 216, 184, 166)}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Did not find an occurrence of the pattern in the current goal"};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_evalRewriteSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rewriteSeq"};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 231, 198, 107, 115, 169, 96, 174)}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalRewriteSeq"};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(131, 252, 0, 80, 225, 242, 251, 126)}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_abortTacticExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__0(lean_object* v___x_31_, lean_object* v___x_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
if (lean_obj_tag(v_a_33_) == 0)
{
lean_object* v___x_35_; 
lean_dec_ref(v___x_31_);
v___x_35_ = l_List_reverse___redArg(v_a_34_);
return v___x_35_;
}
else
{
lean_object* v_head_36_; lean_object* v_tail_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_49_; 
v_head_36_ = lean_ctor_get(v_a_33_, 0);
v_tail_37_ = lean_ctor_get(v_a_33_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_a_33_);
if (v_isSharedCheck_49_ == 0)
{
v___x_39_ = v_a_33_;
v_isShared_40_ = v_isSharedCheck_49_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_tail_37_);
lean_inc(v_head_36_);
lean_dec(v_a_33_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_49_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_41_; lean_object* v_index_42_; uint8_t v___x_43_; 
lean_inc(v_head_36_);
lean_inc_ref(v___x_31_);
v___x_41_ = l_Lean_MetavarContext_getDecl(v___x_31_, v_head_36_);
v_index_42_ = lean_ctor_get(v___x_41_, 6);
lean_inc(v_index_42_);
lean_dec_ref(v___x_41_);
v___x_43_ = lean_nat_dec_le(v___x_32_, v_index_42_);
lean_dec(v_index_42_);
if (v___x_43_ == 0)
{
lean_del_object(v___x_39_);
lean_dec(v_head_36_);
v_a_33_ = v_tail_37_;
goto _start;
}
else
{
lean_object* v___x_46_; 
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 1, v_a_34_);
v___x_46_ = v___x_39_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_head_36_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_a_34_);
v___x_46_ = v_reuseFailAlloc_48_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
v_a_33_ = v_tail_37_;
v_a_34_ = v___x_46_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__0___boxed(lean_object* v___x_50_, lean_object* v___x_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__0(v___x_50_, v___x_51_, v_a_52_, v_a_53_);
lean_dec(v___x_51_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10_spec__14___redArg(lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
return v_x_55_;
}
else
{
lean_object* v_key_57_; lean_object* v_value_58_; lean_object* v_tail_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_82_; 
v_key_57_ = lean_ctor_get(v_x_56_, 0);
v_value_58_ = lean_ctor_get(v_x_56_, 1);
v_tail_59_ = lean_ctor_get(v_x_56_, 2);
v_isSharedCheck_82_ = !lean_is_exclusive(v_x_56_);
if (v_isSharedCheck_82_ == 0)
{
v___x_61_ = v_x_56_;
v_isShared_62_ = v_isSharedCheck_82_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_tail_59_);
lean_inc(v_value_58_);
lean_inc(v_key_57_);
lean_dec(v_x_56_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_82_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; uint64_t v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v_fold_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_63_ = lean_array_get_size(v_x_55_);
v___x_64_ = l_Lean_Expr_hash(v_key_57_);
v___x_65_ = 32ULL;
v___x_66_ = lean_uint64_shift_right(v___x_64_, v___x_65_);
v_fold_67_ = lean_uint64_xor(v___x_64_, v___x_66_);
v___x_68_ = 16ULL;
v___x_69_ = lean_uint64_shift_right(v_fold_67_, v___x_68_);
v___x_70_ = lean_uint64_xor(v_fold_67_, v___x_69_);
v___x_71_ = lean_uint64_to_usize(v___x_70_);
v___x_72_ = lean_usize_of_nat(v___x_63_);
v___x_73_ = ((size_t)1ULL);
v___x_74_ = lean_usize_sub(v___x_72_, v___x_73_);
v___x_75_ = lean_usize_land(v___x_71_, v___x_74_);
v___x_76_ = lean_array_uget_borrowed(v_x_55_, v___x_75_);
lean_inc(v___x_76_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 2, v___x_76_);
v___x_78_ = v___x_61_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_key_57_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_value_58_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v___x_76_);
v___x_78_ = v_reuseFailAlloc_81_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
lean_object* v___x_79_; 
v___x_79_ = lean_array_uset(v_x_55_, v___x_75_, v___x_78_);
v_x_55_ = v___x_79_;
v_x_56_ = v_tail_59_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10___redArg(lean_object* v_i_83_, lean_object* v_source_84_, lean_object* v_target_85_){
_start:
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_array_get_size(v_source_84_);
v___x_87_ = lean_nat_dec_lt(v_i_83_, v___x_86_);
if (v___x_87_ == 0)
{
lean_dec_ref(v_source_84_);
lean_dec(v_i_83_);
return v_target_85_;
}
else
{
lean_object* v_es_88_; lean_object* v___x_89_; lean_object* v_source_90_; lean_object* v_target_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_es_88_ = lean_array_fget(v_source_84_, v_i_83_);
v___x_89_ = lean_box(0);
v_source_90_ = lean_array_fset(v_source_84_, v_i_83_, v___x_89_);
v_target_91_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10_spec__14___redArg(v_target_85_, v_es_88_);
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_add(v_i_83_, v___x_92_);
lean_dec(v_i_83_);
v_i_83_ = v___x_93_;
v_source_84_ = v_source_90_;
v_target_85_ = v_target_91_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7___redArg(lean_object* v_data_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_nbuckets_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_96_ = lean_array_get_size(v_data_95_);
v___x_97_ = lean_unsigned_to_nat(2u);
v_nbuckets_98_ = lean_nat_mul(v___x_96_, v___x_97_);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_box(0);
v___x_101_ = lean_mk_array(v_nbuckets_98_, v___x_100_);
v___x_102_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10___redArg(v___x_99_, v_data_95_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_a_103_, lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
else
{
lean_object* v_key_106_; lean_object* v_tail_107_; uint8_t v___x_108_; 
v_key_106_ = lean_ctor_get(v_x_104_, 0);
v_tail_107_ = lean_ctor_get(v_x_104_, 2);
v___x_108_ = lean_expr_eqv(v_key_106_, v_a_103_);
if (v___x_108_ == 0)
{
v_x_104_ = v_tail_107_;
goto _start;
}
else
{
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_a_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___redArg(v_a_110_, v_x_111_);
lean_dec(v_x_111_);
lean_dec_ref(v_a_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4___redArg(lean_object* v_m_114_, lean_object* v_a_115_, lean_object* v_b_116_){
_start:
{
lean_object* v_size_117_; lean_object* v_buckets_118_; lean_object* v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v_fold_123_; uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v_bkt_132_; uint8_t v___x_133_; 
v_size_117_ = lean_ctor_get(v_m_114_, 0);
v_buckets_118_ = lean_ctor_get(v_m_114_, 1);
v___x_119_ = lean_array_get_size(v_buckets_118_);
v___x_120_ = l_Lean_Expr_hash(v_a_115_);
v___x_121_ = 32ULL;
v___x_122_ = lean_uint64_shift_right(v___x_120_, v___x_121_);
v_fold_123_ = lean_uint64_xor(v___x_120_, v___x_122_);
v___x_124_ = 16ULL;
v___x_125_ = lean_uint64_shift_right(v_fold_123_, v___x_124_);
v___x_126_ = lean_uint64_xor(v_fold_123_, v___x_125_);
v___x_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = lean_usize_of_nat(v___x_119_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v___x_128_, v___x_129_);
v___x_131_ = lean_usize_land(v___x_127_, v___x_130_);
v_bkt_132_ = lean_array_uget_borrowed(v_buckets_118_, v___x_131_);
v___x_133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___redArg(v_a_115_, v_bkt_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_154_; 
lean_inc_ref(v_buckets_118_);
lean_inc(v_size_117_);
v_isSharedCheck_154_ = !lean_is_exclusive(v_m_114_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; lean_object* v_unused_156_; 
v_unused_155_ = lean_ctor_get(v_m_114_, 1);
lean_dec(v_unused_155_);
v_unused_156_ = lean_ctor_get(v_m_114_, 0);
lean_dec(v_unused_156_);
v___x_135_ = v_m_114_;
v_isShared_136_ = v_isSharedCheck_154_;
goto v_resetjp_134_;
}
else
{
lean_dec(v_m_114_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_154_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v_size_x27_138_; lean_object* v___x_139_; lean_object* v_buckets_x27_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_137_ = lean_unsigned_to_nat(1u);
v_size_x27_138_ = lean_nat_add(v_size_117_, v___x_137_);
lean_dec(v_size_117_);
lean_inc(v_bkt_132_);
v___x_139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_139_, 0, v_a_115_);
lean_ctor_set(v___x_139_, 1, v_b_116_);
lean_ctor_set(v___x_139_, 2, v_bkt_132_);
v_buckets_x27_140_ = lean_array_uset(v_buckets_118_, v___x_131_, v___x_139_);
v___x_141_ = lean_unsigned_to_nat(4u);
v___x_142_ = lean_nat_mul(v_size_x27_138_, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(3u);
v___x_144_ = lean_nat_div(v___x_142_, v___x_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_array_get_size(v_buckets_x27_140_);
v___x_146_ = lean_nat_dec_le(v___x_144_, v___x_145_);
lean_dec(v___x_144_);
if (v___x_146_ == 0)
{
lean_object* v_val_147_; lean_object* v___x_149_; 
v_val_147_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7___redArg(v_buckets_x27_140_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_val_147_);
lean_ctor_set(v___x_135_, 0, v_size_x27_138_);
v___x_149_ = v___x_135_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_size_x27_138_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_val_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
lean_object* v___x_152_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_buckets_x27_140_);
lean_ctor_set(v___x_135_, 0, v_size_x27_138_);
v___x_152_ = v___x_135_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_size_x27_138_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_buckets_x27_140_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
lean_dec(v_b_116_);
lean_dec_ref(v_a_115_);
return v_m_114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9___redArg(lean_object* v_mvarId_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; lean_object* v_mctx_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = lean_st_ref_get(v___y_159_);
v_mctx_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc_ref(v_mctx_162_);
lean_dec(v___x_161_);
v___x_163_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_162_, v_mvarId_157_);
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___y_158_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9___redArg___boxed(lean_object* v_mvarId_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9___redArg(v_mvarId_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec(v_mvarId_167_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10___redArg(lean_object* v_mvarId_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; lean_object* v_mctx_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_176_ = lean_st_ref_get(v___y_174_);
v_mctx_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_mctx_177_);
lean_dec(v___x_176_);
v___x_178_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_177_, v_mvarId_172_);
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___y_173_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10___redArg___boxed(lean_object* v_mvarId_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10___redArg(v_mvarId_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec(v_mvarId_182_);
return v_res_186_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3___redArg(lean_object* v_m_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_buckets_189_; lean_object* v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v___x_193_; uint64_t v_fold_194_; uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_buckets_189_ = lean_ctor_get(v_m_187_, 1);
v___x_190_ = lean_array_get_size(v_buckets_189_);
v___x_191_ = l_Lean_Expr_hash(v_a_188_);
v___x_192_ = 32ULL;
v___x_193_ = lean_uint64_shift_right(v___x_191_, v___x_192_);
v_fold_194_ = lean_uint64_xor(v___x_191_, v___x_193_);
v___x_195_ = 16ULL;
v___x_196_ = lean_uint64_shift_right(v_fold_194_, v___x_195_);
v___x_197_ = lean_uint64_xor(v_fold_194_, v___x_196_);
v___x_198_ = lean_uint64_to_usize(v___x_197_);
v___x_199_ = lean_usize_of_nat(v___x_190_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = lean_usize_sub(v___x_199_, v___x_200_);
v___x_202_ = lean_usize_land(v___x_198_, v___x_201_);
v___x_203_ = lean_array_uget_borrowed(v_buckets_189_, v___x_202_);
v___x_204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___redArg(v_a_188_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_m_205_, lean_object* v_a_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3___redArg(v_m_205_, v_a_206_);
lean_dec_ref(v_a_206_);
lean_dec_ref(v_m_205_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1(lean_object* v_mvarId_213_, lean_object* v_e_214_, lean_object* v_a_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_d_226_; lean_object* v_b_227_; lean_object* v___y_228_; uint8_t v___x_234_; 
v___x_234_ = l_Lean_Expr_hasExprMVar(v_e_214_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec_ref(v_e_214_);
v___x_235_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___closed__0));
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_a_215_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
else
{
uint8_t v___x_238_; 
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3___redArg(v_a_215_, v_e_214_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_box(0);
lean_inc_ref(v_e_214_);
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4___redArg(v_a_215_, v_e_214_, v___x_239_);
switch(lean_obj_tag(v_e_214_))
{
case 11:
{
lean_object* v_struct_241_; 
v_struct_241_ = lean_ctor_get(v_e_214_, 2);
lean_inc_ref(v_struct_241_);
lean_dec_ref(v_e_214_);
v_e_214_ = v_struct_241_;
v_a_215_ = v___x_240_;
goto _start;
}
case 7:
{
lean_object* v_binderType_243_; lean_object* v_body_244_; 
v_binderType_243_ = lean_ctor_get(v_e_214_, 1);
lean_inc_ref(v_binderType_243_);
v_body_244_ = lean_ctor_get(v_e_214_, 2);
lean_inc_ref(v_body_244_);
lean_dec_ref(v_e_214_);
v_d_226_ = v_binderType_243_;
v_b_227_ = v_body_244_;
v___y_228_ = v___x_240_;
goto v___jp_225_;
}
case 6:
{
lean_object* v_binderType_245_; lean_object* v_body_246_; 
v_binderType_245_ = lean_ctor_get(v_e_214_, 1);
lean_inc_ref(v_binderType_245_);
v_body_246_ = lean_ctor_get(v_e_214_, 2);
lean_inc_ref(v_body_246_);
lean_dec_ref(v_e_214_);
v_d_226_ = v_binderType_245_;
v_b_227_ = v_body_246_;
v___y_228_ = v___x_240_;
goto v___jp_225_;
}
case 8:
{
lean_object* v_type_247_; lean_object* v_value_248_; lean_object* v_body_249_; lean_object* v___x_250_; 
v_type_247_ = lean_ctor_get(v_e_214_, 1);
lean_inc_ref(v_type_247_);
v_value_248_ = lean_ctor_get(v_e_214_, 2);
lean_inc_ref(v_value_248_);
v_body_249_ = lean_ctor_get(v_e_214_, 3);
lean_inc_ref(v_body_249_);
lean_dec_ref(v_e_214_);
v___x_250_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1(v_mvarId_213_, v_type_247_, v___x_240_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v_fst_252_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
v_fst_252_ = lean_ctor_get(v_a_251_, 0);
if (lean_obj_tag(v_fst_252_) == 0)
{
lean_dec(v_a_251_);
lean_dec_ref(v_body_249_);
lean_dec_ref(v_value_248_);
return v___x_250_;
}
else
{
lean_object* v_snd_253_; lean_object* v___x_254_; 
lean_dec_ref(v___x_250_);
v_snd_253_ = lean_ctor_get(v_a_251_, 1);
lean_inc(v_snd_253_);
lean_dec(v_a_251_);
v___x_254_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1(v_mvarId_213_, v_value_248_, v_snd_253_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v_fst_256_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
v_fst_256_ = lean_ctor_get(v_a_255_, 0);
if (lean_obj_tag(v_fst_256_) == 0)
{
lean_dec(v_a_255_);
lean_dec_ref(v_body_249_);
return v___x_254_;
}
else
{
lean_object* v_snd_257_; 
lean_dec_ref(v___x_254_);
v_snd_257_ = lean_ctor_get(v_a_255_, 1);
lean_inc(v_snd_257_);
lean_dec(v_a_255_);
v_e_214_ = v_body_249_;
v_a_215_ = v_snd_257_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_249_);
return v___x_254_;
}
}
}
else
{
lean_dec_ref(v_body_249_);
lean_dec_ref(v_value_248_);
return v___x_250_;
}
}
case 10:
{
lean_object* v_expr_259_; 
v_expr_259_ = lean_ctor_get(v_e_214_, 1);
lean_inc_ref(v_expr_259_);
lean_dec_ref(v_e_214_);
v_e_214_ = v_expr_259_;
v_a_215_ = v___x_240_;
goto _start;
}
case 5:
{
lean_object* v_fn_261_; lean_object* v_arg_262_; lean_object* v___x_263_; 
v_fn_261_ = lean_ctor_get(v_e_214_, 0);
lean_inc_ref(v_fn_261_);
v_arg_262_ = lean_ctor_get(v_e_214_, 1);
lean_inc_ref(v_arg_262_);
lean_dec_ref(v_e_214_);
v___x_263_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1(v_mvarId_213_, v_fn_261_, v___x_240_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v_fst_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
v_fst_265_ = lean_ctor_get(v_a_264_, 0);
if (lean_obj_tag(v_fst_265_) == 0)
{
lean_dec(v_a_264_);
lean_dec_ref(v_arg_262_);
return v___x_263_;
}
else
{
lean_object* v_snd_266_; 
lean_dec_ref(v___x_263_);
v_snd_266_ = lean_ctor_get(v_a_264_, 1);
lean_inc(v_snd_266_);
lean_dec(v_a_264_);
v_e_214_ = v_arg_262_;
v_a_215_ = v_snd_266_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_262_);
return v___x_263_;
}
}
case 2:
{
lean_object* v_mvarId_268_; lean_object* v___x_269_; 
v_mvarId_268_ = lean_ctor_get(v_e_214_, 0);
lean_inc(v_mvarId_268_);
lean_dec_ref(v_e_214_);
v___x_269_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5(v_mvarId_213_, v_mvarId_268_, v___x_240_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_269_;
}
default: 
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec_ref(v_e_214_);
v___x_270_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___closed__0));
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_240_);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec_ref(v_e_214_);
v___x_273_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___closed__0));
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v_a_215_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
v___jp_225_:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1(v_mvarId_213_, v_d_226_, v___y_228_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v_fst_231_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
v_fst_231_ = lean_ctor_get(v_a_230_, 0);
if (lean_obj_tag(v_fst_231_) == 0)
{
lean_dec(v_a_230_);
lean_dec_ref(v_b_227_);
return v___x_229_;
}
else
{
lean_object* v_snd_232_; 
lean_dec_ref(v___x_229_);
v_snd_232_ = lean_ctor_get(v_a_230_, 1);
lean_inc(v_snd_232_);
lean_dec(v_a_230_);
v_e_214_ = v_b_227_;
v_a_215_ = v_snd_232_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_227_);
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5(lean_object* v_mvarId_276_, lean_object* v_mvarId_x27_277_, lean_object* v_a_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
uint8_t v___x_288_; 
v___x_288_ = l_Lean_instBEqMVarId_beq(v_mvarId_276_, v_mvarId_x27_277_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9___redArg(v_mvarId_x27_277_, v_a_278_, v___y_284_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_373_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_373_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_373_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_373_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_fst_294_; 
v_fst_294_ = lean_ctor_get(v_a_290_, 0);
lean_inc(v_fst_294_);
if (lean_obj_tag(v_fst_294_) == 0)
{
lean_object* v_snd_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_mvarId_x27_277_);
v_snd_295_ = lean_ctor_get(v_a_290_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v_a_290_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; 
v_unused_314_ = lean_ctor_get(v_a_290_, 0);
lean_dec(v_unused_314_);
v___x_297_ = v_a_290_;
v_isShared_298_ = v_isSharedCheck_313_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_snd_295_);
lean_dec(v_a_290_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_313_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_312_; 
v_a_299_ = lean_ctor_get(v_fst_294_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v_fst_294_);
if (v_isSharedCheck_312_ == 0)
{
v___x_301_ = v_fst_294_;
v_isShared_302_ = v_isSharedCheck_312_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v_fst_294_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_312_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_311_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_306_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_304_);
v___x_306_ = v___x_297_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_snd_295_);
v___x_306_ = v_reuseFailAlloc_310_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_308_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_306_);
v___x_308_ = v___x_292_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
}
else
{
lean_object* v_a_315_; 
lean_del_object(v___x_292_);
v_a_315_ = lean_ctor_get(v_fst_294_, 0);
lean_inc(v_a_315_);
lean_dec_ref(v_fst_294_);
if (lean_obj_tag(v_a_315_) == 0)
{
lean_object* v_snd_316_; lean_object* v___x_317_; 
v_snd_316_ = lean_ctor_get(v_a_290_, 1);
lean_inc(v_snd_316_);
lean_dec(v_a_290_);
v___x_317_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10___redArg(v_mvarId_x27_277_, v_snd_316_, v___y_284_);
lean_dec(v_mvarId_x27_277_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_361_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_361_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_361_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_361_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_fst_322_; 
v_fst_322_ = lean_ctor_get(v_a_318_, 0);
lean_inc(v_fst_322_);
if (lean_obj_tag(v_fst_322_) == 0)
{
lean_object* v_snd_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_341_; 
v_snd_323_ = lean_ctor_get(v_a_318_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v_a_318_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; 
v_unused_342_ = lean_ctor_get(v_a_318_, 0);
lean_dec(v_unused_342_);
v___x_325_ = v_a_318_;
v_isShared_326_ = v_isSharedCheck_341_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_snd_323_);
lean_dec(v_a_318_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_341_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_340_; 
v_a_327_ = lean_ctor_get(v_fst_322_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_fst_322_);
if (v_isSharedCheck_340_ == 0)
{
v___x_329_ = v_fst_322_;
v_isShared_330_ = v_isSharedCheck_340_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v_fst_322_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_340_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_339_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_332_);
v___x_334_ = v___x_325_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_snd_323_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_334_);
v___x_336_ = v___x_320_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
else
{
lean_object* v_a_343_; 
v_a_343_ = lean_ctor_get(v_fst_322_, 0);
lean_inc(v_a_343_);
lean_dec_ref(v_fst_322_);
if (lean_obj_tag(v_a_343_) == 0)
{
lean_object* v_snd_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_355_; 
v_snd_344_ = lean_ctor_get(v_a_318_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v_a_318_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; 
v_unused_356_ = lean_ctor_get(v_a_318_, 0);
lean_dec(v_unused_356_);
v___x_346_ = v_a_318_;
v_isShared_347_ = v_isSharedCheck_355_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snd_344_);
lean_dec(v_a_318_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_355_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___closed__0));
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_snd_344_);
v___x_350_ = v_reuseFailAlloc_354_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_352_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_350_);
v___x_352_ = v___x_320_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_val_357_; lean_object* v_snd_358_; lean_object* v_mvarIdPending_359_; 
lean_del_object(v___x_320_);
v_val_357_ = lean_ctor_get(v_a_343_, 0);
lean_inc(v_val_357_);
lean_dec_ref(v_a_343_);
v_snd_358_ = lean_ctor_get(v_a_318_, 1);
lean_inc(v_snd_358_);
lean_dec(v_a_318_);
v_mvarIdPending_359_ = lean_ctor_get(v_val_357_, 1);
lean_inc(v_mvarIdPending_359_);
lean_dec(v_val_357_);
v_mvarId_x27_277_ = v_mvarIdPending_359_;
v_a_278_ = v_snd_358_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_a_362_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_317_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_317_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
else
{
lean_object* v_snd_370_; lean_object* v_val_371_; lean_object* v___x_372_; 
lean_dec(v_mvarId_x27_277_);
v_snd_370_ = lean_ctor_get(v_a_290_, 1);
lean_inc(v_snd_370_);
lean_dec(v_a_290_);
v_val_371_ = lean_ctor_get(v_a_315_, 0);
lean_inc(v_val_371_);
lean_dec_ref(v_a_315_);
v___x_372_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1(v_mvarId_276_, v_val_371_, v_snd_370_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
return v___x_372_;
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_mvarId_x27_277_);
v_a_374_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_289_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_289_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v_mvarId_x27_277_);
v___x_382_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___closed__1));
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v_a_278_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5___boxed(lean_object* v_mvarId_385_, lean_object* v_mvarId_x27_386_, lean_object* v_a_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5(v_mvarId_385_, v_mvarId_x27_386_, v_a_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v_mvarId_385_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1___boxed(lean_object* v_mvarId_398_, lean_object* v_e_399_, lean_object* v_a_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1(v_mvarId_398_, v_e_399_, v_a_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v_mvarId_398_);
return v_res_410_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__0(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_box(0);
v___x_412_ = lean_unsigned_to_nat(16u);
v___x_413_ = lean_mk_array(v___x_412_, v___x_411_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__1(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__0, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__0);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1(lean_object* v_mvarId_417_, lean_object* v_e_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = l_Lean_Expr_hasExprMVar(v_e_418_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref(v_e_418_);
v___x_429_ = 1;
v___x_430_ = lean_box(v___x_429_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__1, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___closed__1);
v___x_433_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1(v_mvarId_417_, v_e_418_, v___x_432_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_448_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_448_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_448_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_448_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_fst_438_; 
v_fst_438_ = lean_ctor_get(v_a_434_, 0);
lean_inc(v_fst_438_);
lean_dec(v_a_434_);
if (lean_obj_tag(v_fst_438_) == 0)
{
uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
lean_dec_ref(v_fst_438_);
v___x_439_ = 0;
v___x_440_ = lean_box(v___x_439_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_440_);
v___x_442_ = v___x_436_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_446_; 
lean_dec_ref(v_fst_438_);
v___x_444_ = lean_box(v___x_428_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_444_);
v___x_446_ = v___x_436_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_433_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_433_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1___boxed(lean_object* v_mvarId_457_, lean_object* v_e_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v_mvarId_457_, v_e_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v_mvarId_457_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3_spec__8(lean_object* v_msgData_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; lean_object* v_env_476_; lean_object* v___x_477_; lean_object* v_mctx_478_; lean_object* v_lctx_479_; lean_object* v_options_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_475_ = lean_st_ref_get(v___y_473_);
v_env_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc_ref(v_env_476_);
lean_dec(v___x_475_);
v___x_477_ = lean_st_ref_get(v___y_471_);
v_mctx_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref(v_mctx_478_);
lean_dec(v___x_477_);
v_lctx_479_ = lean_ctor_get(v___y_470_, 2);
v_options_480_ = lean_ctor_get(v___y_472_, 2);
lean_inc_ref(v_options_480_);
lean_inc_ref(v_lctx_479_);
v___x_481_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_481_, 0, v_env_476_);
lean_ctor_set(v___x_481_, 1, v_mctx_478_);
lean_ctor_set(v___x_481_, 2, v_lctx_479_);
lean_ctor_set(v___x_481_, 3, v_options_480_);
v___x_482_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_msgData_469_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3_spec__8___boxed(lean_object* v_msgData_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3_spec__8(v_msgData_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___redArg(lean_object* v_msg_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_ref_497_; lean_object* v___x_498_; lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_ref_497_ = lean_ctor_get(v___y_494_, 5);
v___x_498_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3_spec__8(v_msg_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_inc(v_ref_497_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_ref_497_);
lean_ctor_set(v___x_503_, 1, v_a_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 1);
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___redArg___boxed(lean_object* v_msg_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___redArg(v_msg_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___redArg(lean_object* v_ref_515_, lean_object* v_msg_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_fileName_526_; lean_object* v_fileMap_527_; lean_object* v_options_528_; lean_object* v_currRecDepth_529_; lean_object* v_maxRecDepth_530_; lean_object* v_ref_531_; lean_object* v_currNamespace_532_; lean_object* v_openDecls_533_; lean_object* v_initHeartbeats_534_; lean_object* v_maxHeartbeats_535_; lean_object* v_quotContext_536_; lean_object* v_currMacroScope_537_; uint8_t v_diag_538_; lean_object* v_cancelTk_x3f_539_; uint8_t v_suppressElabErrors_540_; lean_object* v_inheritedTraceOptions_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_550_; 
v_fileName_526_ = lean_ctor_get(v___y_523_, 0);
v_fileMap_527_ = lean_ctor_get(v___y_523_, 1);
v_options_528_ = lean_ctor_get(v___y_523_, 2);
v_currRecDepth_529_ = lean_ctor_get(v___y_523_, 3);
v_maxRecDepth_530_ = lean_ctor_get(v___y_523_, 4);
v_ref_531_ = lean_ctor_get(v___y_523_, 5);
v_currNamespace_532_ = lean_ctor_get(v___y_523_, 6);
v_openDecls_533_ = lean_ctor_get(v___y_523_, 7);
v_initHeartbeats_534_ = lean_ctor_get(v___y_523_, 8);
v_maxHeartbeats_535_ = lean_ctor_get(v___y_523_, 9);
v_quotContext_536_ = lean_ctor_get(v___y_523_, 10);
v_currMacroScope_537_ = lean_ctor_get(v___y_523_, 11);
v_diag_538_ = lean_ctor_get_uint8(v___y_523_, sizeof(void*)*14);
v_cancelTk_x3f_539_ = lean_ctor_get(v___y_523_, 12);
v_suppressElabErrors_540_ = lean_ctor_get_uint8(v___y_523_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_541_ = lean_ctor_get(v___y_523_, 13);
v_isSharedCheck_550_ = !lean_is_exclusive(v___y_523_);
if (v_isSharedCheck_550_ == 0)
{
v___x_543_ = v___y_523_;
v_isShared_544_ = v_isSharedCheck_550_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_inheritedTraceOptions_541_);
lean_inc(v_cancelTk_x3f_539_);
lean_inc(v_currMacroScope_537_);
lean_inc(v_quotContext_536_);
lean_inc(v_maxHeartbeats_535_);
lean_inc(v_initHeartbeats_534_);
lean_inc(v_openDecls_533_);
lean_inc(v_currNamespace_532_);
lean_inc(v_ref_531_);
lean_inc(v_maxRecDepth_530_);
lean_inc(v_currRecDepth_529_);
lean_inc(v_options_528_);
lean_inc(v_fileMap_527_);
lean_inc(v_fileName_526_);
lean_dec(v___y_523_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_550_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v_ref_545_; lean_object* v___x_547_; 
v_ref_545_ = l_Lean_replaceRef(v_ref_515_, v_ref_531_);
lean_dec(v_ref_531_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 5, v_ref_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_fileName_526_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_fileMap_527_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_options_528_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v_currRecDepth_529_);
lean_ctor_set(v_reuseFailAlloc_549_, 4, v_maxRecDepth_530_);
lean_ctor_set(v_reuseFailAlloc_549_, 5, v_ref_545_);
lean_ctor_set(v_reuseFailAlloc_549_, 6, v_currNamespace_532_);
lean_ctor_set(v_reuseFailAlloc_549_, 7, v_openDecls_533_);
lean_ctor_set(v_reuseFailAlloc_549_, 8, v_initHeartbeats_534_);
lean_ctor_set(v_reuseFailAlloc_549_, 9, v_maxHeartbeats_535_);
lean_ctor_set(v_reuseFailAlloc_549_, 10, v_quotContext_536_);
lean_ctor_set(v_reuseFailAlloc_549_, 11, v_currMacroScope_537_);
lean_ctor_set(v_reuseFailAlloc_549_, 12, v_cancelTk_x3f_539_);
lean_ctor_set(v_reuseFailAlloc_549_, 13, v_inheritedTraceOptions_541_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, sizeof(void*)*14, v_diag_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, sizeof(void*)*14 + 1, v_suppressElabErrors_540_);
v___x_547_ = v_reuseFailAlloc_549_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___redArg(v_msg_516_, v___y_521_, v___y_522_, v___x_547_, v___y_524_);
lean_dec_ref(v___x_547_);
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___redArg___boxed(lean_object* v_ref_551_, lean_object* v_msg_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___redArg(v_ref_551_, v_msg_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v_ref_551_);
return v_res_562_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__1(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__0));
v___x_565_ = l_Lean_stringToMessageData(v___x_564_);
return v___x_565_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__3(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__2));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite(lean_object* v_mvarId_569_, lean_object* v_e_570_, lean_object* v_stx_571_, uint8_t v_symm_572_, lean_object* v_config_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; 
v___x_583_ = lean_st_ref_get(v_a_579_);
v___x_584_ = lean_box(0);
v___x_585_ = 1;
lean_inc(v_a_581_);
lean_inc_ref(v_a_580_);
lean_inc(v_a_579_);
lean_inc_ref(v_a_578_);
lean_inc(v_a_577_);
lean_inc_ref(v_a_576_);
lean_inc(v_a_575_);
lean_inc_ref(v_a_574_);
lean_inc(v_stx_571_);
v___x_586_ = l_Lean_Elab_Tactic_elabTerm(v_stx_571_, v___x_584_, v___x_585_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_mctx_587_; lean_object* v_a_588_; lean_object* v_mvarCounter_589_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; uint8_t v___x_655_; 
v_mctx_587_ = lean_ctor_get(v___x_583_, 0);
lean_inc_ref(v_mctx_587_);
lean_dec(v___x_583_);
v_a_588_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_588_);
lean_dec_ref(v___x_586_);
v_mvarCounter_589_ = lean_ctor_get(v_mctx_587_, 2);
lean_inc(v_mvarCounter_589_);
lean_dec_ref(v_mctx_587_);
v___x_655_ = l_Lean_Expr_hasSyntheticSorry(v_a_588_);
if (v___x_655_ == 0)
{
v___y_619_ = v_a_574_;
v___y_620_ = v_a_575_;
v___y_621_ = v_a_576_;
v___y_622_ = v_a_577_;
v___y_623_ = v_a_578_;
v___y_624_ = v_a_579_;
v___y_625_ = v_a_580_;
v___y_626_ = v_a_581_;
goto v___jp_618_;
}
else
{
lean_object* v___x_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v_mvarCounter_589_);
lean_dec(v_a_588_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec_ref(v_config_573_);
lean_dec(v_stx_571_);
lean_dec_ref(v_e_570_);
lean_dec(v_mvarId_569_);
v___x_656_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg();
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
v___jp_590_:
{
lean_object* v___x_595_; 
lean_inc(v___y_592_);
v___x_595_ = l_Lean_MVarId_rewrite(v_mvarId_569_, v_e_570_, v_a_588_, v_symm_572_, v_config_573_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_617_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_617_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_617_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_617_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v_mctx_601_; lean_object* v_eNew_602_; lean_object* v_eqProof_603_; lean_object* v_mvarIds_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_616_; 
v___x_600_ = lean_st_ref_get(v___y_592_);
lean_dec(v___y_592_);
v_mctx_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc_ref(v_mctx_601_);
lean_dec(v___x_600_);
v_eNew_602_ = lean_ctor_get(v_a_596_, 0);
v_eqProof_603_ = lean_ctor_get(v_a_596_, 1);
v_mvarIds_604_ = lean_ctor_get(v_a_596_, 2);
v_isSharedCheck_616_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_616_ == 0)
{
v___x_606_ = v_a_596_;
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_mvarIds_604_);
lean_inc(v_eqProof_603_);
lean_inc(v_eNew_602_);
lean_dec(v_a_596_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_608_ = lean_box(0);
v___x_609_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__0(v_mctx_601_, v_mvarCounter_589_, v_mvarIds_604_, v___x_608_);
lean_dec(v_mvarCounter_589_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 2, v___x_609_);
v___x_611_ = v___x_606_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_eNew_602_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_eqProof_603_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v___x_609_);
v___x_611_ = v_reuseFailAlloc_615_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_611_);
v___x_613_ = v___x_598_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
else
{
lean_dec(v___y_592_);
lean_dec(v_mvarCounter_589_);
return v___x_595_;
}
}
v___jp_618_:
{
lean_object* v___x_627_; 
lean_inc(v_a_588_);
v___x_627_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v_mvarId_569_, v_a_588_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; uint8_t v___x_629_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref(v___x_627_);
v___x_629_ = lean_unbox(v_a_628_);
lean_dec(v_a_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_mvarCounter_589_);
lean_dec_ref(v_config_573_);
lean_dec_ref(v_e_570_);
v___x_630_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__1, &l_Lean_Elab_Tactic_elabRewrite___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__1);
v___x_631_ = l_Lean_indentExpr(v_a_588_);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__3, &l_Lean_Elab_Tactic_elabRewrite___closed__3_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__3);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_Expr_mvar___override(v_mvarId_569_);
v___x_636_ = l_Lean_MessageData_ofExpr(v___x_635_);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_634_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___redArg(v_stx_571_, v___x_637_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v_stx_571_);
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v_stx_571_);
v___y_591_ = v___y_623_;
v___y_592_ = v___y_624_;
v___y_593_ = v___y_625_;
v___y_594_ = v___y_626_;
goto v___jp_590_;
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v_mvarCounter_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_config_573_);
lean_dec(v_stx_571_);
lean_dec_ref(v_e_570_);
lean_dec(v_mvarId_569_);
v_a_647_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_627_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_627_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v___x_583_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec_ref(v_config_573_);
lean_dec(v_stx_571_);
lean_dec_ref(v_e_570_);
lean_dec(v_mvarId_569_);
v_a_665_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_586_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_586_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___boxed(lean_object* v_mvarId_673_, lean_object* v_e_674_, lean_object* v_stx_675_, lean_object* v_symm_676_, lean_object* v_config_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
uint8_t v_symm_boxed_687_; lean_object* v_res_688_; 
v_symm_boxed_687_ = lean_unbox(v_symm_676_);
v_res_688_ = l_Lean_Elab_Tactic_elabRewrite(v_mvarId_673_, v_e_674_, v_stx_675_, v_symm_boxed_687_, v_config_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2(lean_object* v_00_u03b1_689_, lean_object* v_ref_690_, lean_object* v_msg_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___redArg(v_ref_690_, v_msg_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___boxed(lean_object* v_00_u03b1_702_, lean_object* v_ref_703_, lean_object* v_msg_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_00_u03b1_702_, v_ref_703_, v_msg_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v_ref_703_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3(lean_object* v_00_u03b1_715_, lean_object* v_msg_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___redArg(v_msg_716_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___boxed(lean_object* v_00_u03b1_727_, lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3(v_00_u03b1_727_, v_msg_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_738_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_739_, lean_object* v_m_740_, lean_object* v_a_741_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3___redArg(v_m_740_, v_a_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_743_, lean_object* v_m_744_, lean_object* v_a_745_){
_start:
{
uint8_t v_res_746_; lean_object* v_r_747_; 
v_res_746_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3(v_00_u03b2_743_, v_m_744_, v_a_745_);
lean_dec_ref(v_a_745_);
lean_dec_ref(v_m_744_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_748_, lean_object* v_m_749_, lean_object* v_a_750_, lean_object* v_b_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4___redArg(v_m_749_, v_a_750_, v_b_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9(lean_object* v_mvarId_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9___redArg(v_mvarId_753_, v___y_754_, v___y_760_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9___boxed(lean_object* v_mvarId_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9(v_mvarId_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v_mvarId_765_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10(lean_object* v_mvarId_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10___redArg(v_mvarId_777_, v___y_778_, v___y_784_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10___boxed(lean_object* v_mvarId_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10(v_mvarId_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v_mvarId_789_);
return v_res_800_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_801_, lean_object* v_a_802_, lean_object* v_x_803_){
_start:
{
uint8_t v___x_804_; 
v___x_804_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___redArg(v_a_802_, v_x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_805_, lean_object* v_a_806_, lean_object* v_x_807_){
_start:
{
uint8_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_805_, v_a_806_, v_x_807_);
lean_dec(v_x_807_);
lean_dec_ref(v_a_806_);
v_r_809_ = lean_box(v_res_808_);
return v_r_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_810_, lean_object* v_data_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7___redArg(v_data_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_813_, lean_object* v_i_814_, lean_object* v_source_815_, lean_object* v_target_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10___redArg(v_i_814_, v_source_815_, v_target_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10_spec__14(lean_object* v_00_u03b2_818_, lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10_spec__14___redArg(v_x_819_, v_x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(lean_object* v_mvarId_822_, lean_object* v_x_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_822_, v_x_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_a_838_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_829_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_829_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg___boxed(lean_object* v_mvarId_846_, lean_object* v_x_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_846_, v_x_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(lean_object* v_00_u03b1_854_, lean_object* v_mvarId_855_, lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_855_, v_x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___boxed(lean_object* v_00_u03b1_863_, lean_object* v_mvarId_864_, lean_object* v_x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(v_00_u03b1_863_, v_mvarId_864_, v_x_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
return v_res_871_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_872_, lean_object* v_i_873_, lean_object* v_k_874_){
_start:
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = lean_array_get_size(v_keys_872_);
v___x_876_ = lean_nat_dec_lt(v_i_873_, v___x_875_);
if (v___x_876_ == 0)
{
lean_dec(v_i_873_);
return v___x_876_;
}
else
{
lean_object* v_k_x27_877_; uint8_t v___x_878_; 
v_k_x27_877_ = lean_array_fget_borrowed(v_keys_872_, v_i_873_);
v___x_878_ = l_Lean_instBEqMVarId_beq(v_k_874_, v_k_x27_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = lean_nat_add(v_i_873_, v___x_879_);
lean_dec(v_i_873_);
v_i_873_ = v___x_880_;
goto _start;
}
else
{
lean_dec(v_i_873_);
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_882_, lean_object* v_i_883_, lean_object* v_k_884_){
_start:
{
uint8_t v_res_885_; lean_object* v_r_886_; 
v_res_885_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_882_, v_i_883_, v_k_884_);
lean_dec(v_k_884_);
lean_dec_ref(v_keys_882_);
v_r_886_ = lean_box(v_res_885_);
return v_r_886_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_887_; size_t v___x_888_; size_t v___x_889_; 
v___x_887_ = ((size_t)5ULL);
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_shift_left(v___x_888_, v___x_887_);
return v___x_889_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; 
v___x_890_ = ((size_t)1ULL);
v___x_891_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_892_ = lean_usize_sub(v___x_891_, v___x_890_);
return v___x_892_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(lean_object* v_x_893_, size_t v_x_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_object* v_es_896_; lean_object* v___x_897_; size_t v___x_898_; size_t v___x_899_; size_t v___x_900_; lean_object* v_j_901_; lean_object* v___x_902_; 
v_es_896_ = lean_ctor_get(v_x_893_, 0);
lean_inc_ref(v_es_896_);
lean_dec_ref(v_x_893_);
v___x_897_ = lean_box(2);
v___x_898_ = ((size_t)5ULL);
v___x_899_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_900_ = lean_usize_land(v_x_894_, v___x_899_);
v_j_901_ = lean_usize_to_nat(v___x_900_);
v___x_902_ = lean_array_get(v___x_897_, v_es_896_, v_j_901_);
lean_dec(v_j_901_);
lean_dec_ref(v_es_896_);
switch(lean_obj_tag(v___x_902_))
{
case 0:
{
lean_object* v_key_903_; uint8_t v___x_904_; 
v_key_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_key_903_);
lean_dec_ref(v___x_902_);
v___x_904_ = l_Lean_instBEqMVarId_beq(v_x_895_, v_key_903_);
lean_dec(v_key_903_);
return v___x_904_;
}
case 1:
{
lean_object* v_node_905_; size_t v___x_906_; 
v_node_905_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_node_905_);
lean_dec_ref(v___x_902_);
v___x_906_ = lean_usize_shift_right(v_x_894_, v___x_898_);
v_x_893_ = v_node_905_;
v_x_894_ = v___x_906_;
goto _start;
}
default: 
{
uint8_t v___x_908_; 
v___x_908_ = 0;
return v___x_908_;
}
}
}
else
{
lean_object* v_ks_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_ks_909_ = lean_ctor_get(v_x_893_, 0);
lean_inc_ref(v_ks_909_);
lean_dec_ref(v_x_893_);
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_909_, v___x_910_, v_x_895_);
lean_dec_ref(v_ks_909_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
size_t v_x_2294__boxed_915_; uint8_t v_res_916_; lean_object* v_r_917_; 
v_x_2294__boxed_915_ = lean_unbox_usize(v_x_913_);
lean_dec(v_x_913_);
v_res_916_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_912_, v_x_2294__boxed_915_, v_x_914_);
lean_dec(v_x_914_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
uint64_t v___x_920_; size_t v___x_921_; uint8_t v___x_922_; 
v___x_920_ = l_Lean_instHashableMVarId_hash(v_x_919_);
v___x_921_ = lean_uint64_to_usize(v___x_920_);
v___x_922_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_918_, v___x_921_, v_x_919_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
uint8_t v_res_925_; lean_object* v_r_926_; 
v_res_925_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_923_, v_x_924_);
lean_dec(v_x_924_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(lean_object* v_mvarId_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; lean_object* v_mctx_931_; lean_object* v_eAssignment_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_930_ = lean_st_ref_get(v___y_928_);
v_mctx_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc_ref(v_mctx_931_);
lean_dec(v___x_930_);
v_eAssignment_932_ = lean_ctor_get(v_mctx_931_, 7);
lean_inc_ref(v_eAssignment_932_);
lean_dec_ref(v_mctx_931_);
v___x_933_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_eAssignment_932_, v_mvarId_927_);
v___x_934_ = lean_box(v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg___boxed(lean_object* v_mvarId_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec(v_mvarId_936_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
if (lean_obj_tag(v_x_940_) == 0)
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_x_941_);
return v___x_947_;
}
else
{
lean_object* v_head_948_; lean_object* v_tail_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_962_; 
v_head_948_ = lean_ctor_get(v_x_940_, 0);
v_tail_949_ = lean_ctor_get(v_x_940_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_x_940_);
if (v_isSharedCheck_962_ == 0)
{
v___x_951_ = v_x_940_;
v_isShared_952_ = v_isSharedCheck_962_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_tail_949_);
lean_inc(v_head_948_);
lean_dec(v_x_940_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_962_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_958_; lean_object* v_a_959_; uint8_t v___x_960_; 
v___x_958_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_head_948_, v___y_943_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref(v___x_958_);
v___x_960_ = lean_unbox(v_a_959_);
lean_dec(v_a_959_);
if (v___x_960_ == 0)
{
goto v___jp_953_;
}
else
{
lean_del_object(v___x_951_);
lean_dec(v_head_948_);
v_x_940_ = v_tail_949_;
goto _start;
}
v___jp_953_:
{
lean_object* v___x_955_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v_x_941_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_head_948_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_x_941_);
v___x_955_ = v_reuseFailAlloc_957_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
v_x_940_ = v_tail_949_;
v_x_941_ = v___x_955_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3___boxed(lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_x_963_, v_x_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(lean_object* v_head_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
lean_inc(v_head_971_);
v___x_977_ = l_Lean_MVarId_getType(v_head_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref(v___x_977_);
lean_inc(v___y_973_);
v___x_979_ = l_Lean_Meta_isProp(v_a_978_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_991_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_991_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_991_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_991_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
uint8_t v___x_984_; 
v___x_984_ = lean_unbox(v_a_980_);
lean_dec(v_a_980_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_987_; 
lean_dec(v___y_973_);
lean_dec(v_head_971_);
v___x_985_ = lean_box(0);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_985_);
v___x_987_ = v___x_982_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
uint8_t v___x_989_; lean_object* v___x_990_; 
lean_del_object(v___x_982_);
v___x_989_ = 2;
v___x_990_ = l_Lean_MVarId_setKind___redArg(v_head_971_, v___x_989_, v___y_973_);
lean_dec(v___y_973_);
return v___x_990_;
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v___y_973_);
lean_dec(v_head_971_);
v_a_992_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_979_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_979_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v_head_971_);
v_a_1000_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_977_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_977_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed(lean_object* v_head_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(v_head_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(lean_object* v_as_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
if (lean_obj_tag(v_as_1015_) == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
else
{
lean_object* v_head_1023_; lean_object* v_tail_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; 
v_head_1023_ = lean_ctor_get(v_as_1015_, 0);
lean_inc(v_head_1023_);
v_tail_1024_ = lean_ctor_get(v_as_1015_, 1);
lean_inc(v_tail_1024_);
lean_dec_ref(v_as_1015_);
lean_inc(v_head_1023_);
v___f_1025_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1025_, 0, v_head_1023_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
v___x_1026_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_head_1023_, v___f_1025_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_dec_ref(v___x_1026_);
v_as_1015_ = v_tail_1024_;
goto _start;
}
else
{
lean_dec(v_tail_1024_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v___x_1026_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___boxed(lean_object* v_as_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_as_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite(lean_object* v_r_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_eNew_1041_; lean_object* v_eqProof_1042_; lean_object* v_mvarIds_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1082_; 
v_eNew_1041_ = lean_ctor_get(v_r_1035_, 0);
v_eqProof_1042_ = lean_ctor_get(v_r_1035_, 1);
v_mvarIds_1043_ = lean_ctor_get(v_r_1035_, 2);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_r_1035_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1045_ = v_r_1035_;
v_isShared_1046_ = v_isSharedCheck_1082_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_mvarIds_1043_);
lean_inc(v_eqProof_1042_);
lean_inc(v_eNew_1041_);
lean_dec(v_r_1035_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1082_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v_a_1048_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_box(0);
v___x_1070_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_mvarIds_1043_, v___x_1069_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref(v___x_1070_);
v___x_1072_ = l_List_reverse___redArg(v_a_1071_);
v_a_1048_ = v___x_1072_;
goto v___jp_1047_;
}
else
{
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1073_; 
v_a_1073_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1073_);
lean_dec_ref(v___x_1070_);
v_a_1048_ = v_a_1073_;
goto v___jp_1047_;
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_del_object(v___x_1045_);
lean_dec_ref(v_eqProof_1042_);
lean_dec_ref(v_eNew_1041_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
v_a_1074_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1070_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1070_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
v___jp_1047_:
{
lean_object* v___x_1049_; 
lean_inc(v_a_1048_);
v___x_1049_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_a_1048_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1059_; 
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v___x_1049_, 0);
lean_dec(v_unused_1060_);
v___x_1051_ = v___x_1049_;
v_isShared_1052_ = v_isSharedCheck_1059_;
goto v_resetjp_1050_;
}
else
{
lean_dec(v___x_1049_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1059_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 2, v_a_1048_);
v___x_1054_ = v___x_1045_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_eNew_1041_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_eqProof_1042_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_a_1048_);
v___x_1054_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1056_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1054_);
v___x_1056_ = v___x_1051_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_a_1048_);
lean_del_object(v___x_1045_);
lean_dec_ref(v_eqProof_1042_);
lean_dec_ref(v_eNew_1041_);
v_a_1061_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1049_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1049_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite___boxed(lean_object* v_r_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Elab_Tactic_finishElabRewrite(v_r_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(lean_object* v_mvarId_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1090_, v___y_1092_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___boxed(lean_object* v_mvarId_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(v_mvarId_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v_mvarId_1097_);
return v_res_1103_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(lean_object* v_00_u03b2_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_){
_start:
{
uint8_t v___x_1107_; 
v___x_1107_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1105_, v_x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(v_00_u03b2_1108_, v_x_1109_, v_x_1110_);
lean_dec(v_x_1110_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1113_, lean_object* v_x_1114_, size_t v_x_1115_, lean_object* v_x_1116_){
_start:
{
uint8_t v___x_1117_; 
v___x_1117_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1114_, v_x_1115_, v_x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1118_, lean_object* v_x_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
size_t v_x_2651__boxed_1122_; uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_x_2651__boxed_1122_ = lean_unbox_usize(v_x_1120_);
lean_dec(v_x_1120_);
v_res_1123_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(v_00_u03b2_1118_, v_x_1119_, v_x_2651__boxed_1122_, v_x_1121_);
lean_dec(v_x_1121_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1125_, lean_object* v_keys_1126_, lean_object* v_vals_1127_, lean_object* v_heq_1128_, lean_object* v_i_1129_, lean_object* v_k_1130_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1126_, v_i_1129_, v_k_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1132_, lean_object* v_keys_1133_, lean_object* v_vals_1134_, lean_object* v_heq_1135_, lean_object* v_i_1136_, lean_object* v_k_1137_){
_start:
{
uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1132_, v_keys_1133_, v_vals_1134_, v_heq_1135_, v_i_1136_, v_k_1137_);
lean_dec(v_k_1137_);
lean_dec_ref(v_vals_1134_);
lean_dec_ref(v_keys_1133_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object* v_stx_1140_, uint8_t v_symm_1141_, lean_object* v_config_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1144_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1154_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = l_Lean_Elab_Tactic_getMainTarget(v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref(v___x_1154_);
v___x_1156_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1153_, v_a_1155_, v_stx_1140_, v_symm_1141_, v_config_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1156_;
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec(v_a_1153_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec_ref(v_config_1142_);
lean_dec(v_stx_1140_);
v_a_1157_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1154_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1154_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec_ref(v_config_1142_);
lean_dec(v_stx_1140_);
v_a_1165_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1152_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1152_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object* v_stx_1173_, lean_object* v_symm_1174_, lean_object* v_config_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
uint8_t v_symm_boxed_1185_; lean_object* v_res_1186_; 
v_symm_boxed_1185_ = lean_unbox(v_symm_1174_);
v_res_1186_ = l_Lean_Elab_Tactic_rewriteTarget___lam__0(v_stx_1173_, v_symm_boxed_1185_, v_config_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object* v_stx_1187_, uint8_t v_symm_1188_, lean_object* v_config_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v___x_1199_; lean_object* v___f_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1199_ = lean_box(v_symm_1188_);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1200_, 0, v_stx_1187_);
lean_closure_set(v___f_1200_, 1, v___x_1199_);
lean_closure_set(v___f_1200_, 2, v_config_1189_);
v___x_1201_ = 1;
lean_inc(v_a_1191_);
v___x_1202_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1202_, 0, lean_box(0));
lean_closure_set(v___x_1202_, 1, v___f_1200_);
lean_closure_set(v___x_1202_, 2, v_a_1190_);
lean_closure_set(v___x_1202_, 3, v_a_1191_);
lean_inc(v_a_1197_);
lean_inc_ref(v_a_1196_);
lean_inc(v_a_1195_);
lean_inc_ref(v_a_1194_);
v___x_1203_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1202_, v___x_1201_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1205_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref(v___x_1203_);
lean_inc(v_a_1197_);
lean_inc_ref(v_a_1196_);
lean_inc(v_a_1195_);
lean_inc_ref(v_a_1194_);
v___x_1205_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1204_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1207_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref(v___x_1205_);
v___x_1207_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1191_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v_eNew_1209_; lean_object* v_eqProof_1210_; lean_object* v_mvarIds_1211_; lean_object* v___x_1212_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref(v___x_1207_);
v_eNew_1209_ = lean_ctor_get(v_a_1206_, 0);
lean_inc_ref(v_eNew_1209_);
v_eqProof_1210_ = lean_ctor_get(v_a_1206_, 1);
lean_inc_ref(v_eqProof_1210_);
v_mvarIds_1211_ = lean_ctor_get(v_a_1206_, 2);
lean_inc(v_mvarIds_1211_);
lean_dec(v_a_1206_);
lean_inc(v_a_1197_);
lean_inc_ref(v_a_1196_);
lean_inc(v_a_1195_);
lean_inc_ref(v_a_1194_);
v___x_1212_ = l_Lean_MVarId_replaceTargetEq(v_a_1208_, v_eNew_1209_, v_eqProof_1210_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_a_1213_);
lean_ctor_set(v___x_1214_, 1, v_mvarIds_1211_);
v___x_1215_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1214_, v_a_1191_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1191_);
return v___x_1215_;
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_mvarIds_1211_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1191_);
v_a_1216_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1212_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1212_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_a_1206_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1191_);
v_a_1224_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1207_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1207_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1191_);
v_a_1232_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1205_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1205_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1191_);
v_a_1240_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1203_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1203_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object* v_stx_1248_, lean_object* v_symm_1249_, lean_object* v_config_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
uint8_t v_symm_boxed_1260_; lean_object* v_res_1261_; 
v_symm_boxed_1260_ = lean_unbox(v_symm_1249_);
v_res_1261_ = l_Lean_Elab_Tactic_rewriteTarget(v_stx_1248_, v_symm_boxed_1260_, v_config_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(lean_object* v_fvarId_1262_, lean_object* v_stx_1263_, uint8_t v_symm_1264_, lean_object* v_config_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
lean_inc_ref(v___y_1270_);
v___x_1275_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1262_, v___y_1270_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1267_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = l_Lean_LocalDecl_type(v_a_1276_);
lean_dec(v_a_1276_);
v___x_1280_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1278_, v___x_1279_, v_stx_1263_, v_symm_1264_, v_config_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1280_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_a_1276_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec_ref(v_config_1265_);
lean_dec(v_stx_1263_);
v_a_1281_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1277_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1277_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec_ref(v_config_1265_);
lean_dec(v_stx_1263_);
v_a_1289_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1275_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1275_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed(lean_object* v_fvarId_1297_, lean_object* v_stx_1298_, lean_object* v_symm_1299_, lean_object* v_config_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
uint8_t v_symm_boxed_1310_; lean_object* v_res_1311_; 
v_symm_boxed_1310_ = lean_unbox(v_symm_1299_);
v_res_1311_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(v_fvarId_1297_, v_stx_1298_, v_symm_boxed_1310_, v_config_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(lean_object* v___f_1312_, uint8_t v___x_1313_, lean_object* v_fvarId_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_inc(v___y_1316_);
v___x_1324_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1324_, 0, lean_box(0));
lean_closure_set(v___x_1324_, 1, v___f_1312_);
lean_closure_set(v___x_1324_, 2, v___y_1315_);
lean_closure_set(v___x_1324_, 3, v___y_1316_);
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
v___x_1325_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1324_, v___x_1313_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1325_);
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
v___x_1327_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1326_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1316_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v_eNew_1331_; lean_object* v_eqProof_1332_; lean_object* v_mvarIds_1333_; lean_object* v___x_1334_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref(v___x_1329_);
v_eNew_1331_ = lean_ctor_get(v_a_1328_, 0);
lean_inc_ref(v_eNew_1331_);
v_eqProof_1332_ = lean_ctor_get(v_a_1328_, 1);
lean_inc_ref(v_eqProof_1332_);
v_mvarIds_1333_ = lean_ctor_get(v_a_1328_, 2);
lean_inc(v_mvarIds_1333_);
lean_dec(v_a_1328_);
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
v___x_1334_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(v_a_1330_, v_fvarId_1314_, v_eNew_1331_, v_eqProof_1332_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v_mvarId_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref(v___x_1334_);
v_mvarId_1336_ = lean_ctor_get(v_a_1335_, 1);
lean_inc(v_mvarId_1336_);
lean_dec(v_a_1335_);
v___x_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_mvarId_1336_);
lean_ctor_set(v___x_1337_, 1, v_mvarIds_1333_);
v___x_1338_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1337_, v___y_1316_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1316_);
return v___x_1338_;
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_mvarIds_1333_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1316_);
v_a_1339_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1334_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1334_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec(v_a_1328_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1316_);
lean_dec(v_fvarId_1314_);
v_a_1347_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1329_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1329_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1316_);
lean_dec(v_fvarId_1314_);
v_a_1355_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1327_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1327_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1316_);
lean_dec(v_fvarId_1314_);
v_a_1363_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1325_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1325_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed(lean_object* v___f_1371_, lean_object* v___x_1372_, lean_object* v_fvarId_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v___x_1052__boxed_1383_; lean_object* v_res_1384_; 
v___x_1052__boxed_1383_ = lean_unbox(v___x_1372_);
v_res_1384_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(v___f_1371_, v___x_1052__boxed_1383_, v_fvarId_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object* v_stx_1385_, uint8_t v_symm_1386_, lean_object* v_fvarId_1387_, lean_object* v_config_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v___f_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; 
v___x_1398_ = lean_box(v_symm_1386_);
lean_inc(v_fvarId_1387_);
v___f_1399_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1399_, 0, v_fvarId_1387_);
lean_closure_set(v___f_1399_, 1, v_stx_1385_);
lean_closure_set(v___f_1399_, 2, v___x_1398_);
lean_closure_set(v___f_1399_, 3, v_config_1388_);
v___x_1400_ = 1;
v___x_1401_ = lean_box(v___x_1400_);
v___f_1402_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed), 12, 3);
lean_closure_set(v___f_1402_, 0, v___f_1399_);
lean_closure_set(v___f_1402_, 1, v___x_1401_);
lean_closure_set(v___f_1402_, 2, v_fvarId_1387_);
v___x_1403_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1402_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object* v_stx_1404_, lean_object* v_symm_1405_, lean_object* v_fvarId_1406_, lean_object* v_config_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
uint8_t v_symm_boxed_1417_; lean_object* v_res_1418_; 
v_symm_boxed_1417_ = lean_unbox(v_symm_1405_);
v_res_1418_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_stx_1404_, v_symm_boxed_1417_, v_fvarId_1406_, v_config_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
return v_res_1418_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0));
v___x_1421_ = l_Lean_stringToMessageData(v___x_1420_);
return v___x_1421_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2));
v___x_1424_ = l_Lean_stringToMessageData(v___x_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(lean_object* v_x_1425_, uint8_t v_symm_1426_, lean_object* v_id_1427_, lean_object* v_declName_1428_, lean_object* v_hint_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
if (lean_obj_tag(v_a_1430_) == 0)
{
lean_object* v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec_ref(v_x_1425_);
v___x_1440_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1);
v___x_1441_ = 0;
v___x_1442_ = l_Lean_MessageData_ofConstName(v_declName_1428_, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1440_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v_hint_1429_);
v___x_1447_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___redArg(v___x_1446_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
return v___x_1447_;
}
else
{
lean_object* v_head_1448_; lean_object* v_tail_1449_; lean_object* v___x_1450_; 
v_head_1448_ = lean_ctor_get(v_a_1430_, 0);
lean_inc(v_head_1448_);
v_tail_1449_ = lean_ctor_get(v_a_1430_, 1);
lean_inc(v_tail_1449_);
lean_dec_ref(v_a_1430_);
v___x_1450_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1432_, v_a_1434_, v_a_1436_, v_a_1438_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; uint8_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1450_);
v___x_1452_ = 0;
v___x_1453_ = l_Lean_mkCIdentFrom(v_id_1427_, v_head_1448_, v___x_1452_);
v___x_1454_ = lean_box(v_symm_1426_);
lean_inc_ref(v_x_1425_);
v___x_1455_ = lean_apply_2(v_x_1425_, v___x_1454_, v___x_1453_);
lean_inc(v_a_1438_);
lean_inc_ref(v_a_1437_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
lean_inc(v_a_1434_);
lean_inc_ref(v_a_1433_);
lean_inc(v_a_1432_);
lean_inc_ref(v_a_1431_);
v___x_1456_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_1455_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_dec(v_a_1451_);
lean_dec(v_tail_1449_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec_ref(v_hint_1429_);
lean_dec(v_declName_1428_);
lean_dec_ref(v_x_1425_);
return v___x_1456_;
}
else
{
lean_object* v_a_1457_; uint8_t v___y_1459_; uint8_t v___x_1462_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
v___x_1462_ = l_Lean_Exception_isInterrupt(v_a_1457_);
if (v___x_1462_ == 0)
{
uint8_t v___x_1463_; 
v___x_1463_ = l_Lean_Exception_isRuntime(v_a_1457_);
v___y_1459_ = v___x_1463_;
goto v___jp_1458_;
}
else
{
lean_dec(v_a_1457_);
v___y_1459_ = v___x_1462_;
goto v___jp_1458_;
}
v___jp_1458_:
{
if (v___y_1459_ == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v___x_1456_);
v___x_1460_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1451_, v___y_1459_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_dec_ref(v___x_1460_);
v_a_1430_ = v_tail_1449_;
goto _start;
}
else
{
lean_dec(v_tail_1449_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec_ref(v_hint_1429_);
lean_dec(v_declName_1428_);
lean_dec_ref(v_x_1425_);
return v___x_1460_;
}
}
else
{
lean_dec(v_a_1451_);
lean_dec(v_tail_1449_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec_ref(v_hint_1429_);
lean_dec(v_declName_1428_);
lean_dec_ref(v_x_1425_);
return v___x_1456_;
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_tail_1449_);
lean_dec(v_head_1448_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec_ref(v_hint_1429_);
lean_dec(v_declName_1428_);
lean_dec_ref(v_x_1425_);
v_a_1464_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1450_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1450_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___boxed(lean_object* v_x_1472_, lean_object* v_symm_1473_, lean_object* v_id_1474_, lean_object* v_declName_1475_, lean_object* v_hint_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
uint8_t v_symm_boxed_1487_; lean_object* v_res_1488_; 
v_symm_boxed_1487_ = lean_unbox(v_symm_1473_);
v_res_1488_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(v_x_1472_, v_symm_boxed_1487_, v_id_1474_, v_declName_1475_, v_hint_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
lean_dec(v_id_1474_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object* v_a_1489_, lean_object* v_trees_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_apply_9(v_a_1489_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, lean_box(0));
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1509_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1509_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1509_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_a_1501_);
lean_ctor_set(v___x_1505_, 1, v_trees_1490_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1505_);
v___x_1507_ = v___x_1503_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_trees_1490_);
v_a_1510_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1500_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1500_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object* v_a_1518_, lean_object* v_trees_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(v_a_1518_, v_trees_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(lean_object* v___x_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1530_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1___boxed(lean_object* v___x_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(v___x_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(lean_object* v___y_1552_, lean_object* v_mkInfoTree_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v_a_1561_, lean_object* v_a_x3f_1562_){
_start:
{
lean_object* v___x_1564_; lean_object* v_infoState_1565_; lean_object* v_trees_1566_; lean_object* v___x_1567_; 
v___x_1564_ = lean_st_ref_get(v___y_1552_);
v_infoState_1565_ = lean_ctor_get(v___x_1564_, 7);
lean_inc_ref(v_infoState_1565_);
lean_dec(v___x_1564_);
v_trees_1566_ = lean_ctor_get(v_infoState_1565_, 2);
lean_inc_ref(v_trees_1566_);
lean_dec_ref(v_infoState_1565_);
lean_inc(v___y_1552_);
v___x_1567_ = lean_apply_10(v_mkInfoTree_1553_, v_trees_1566_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1552_, lean_box(0));
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1606_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1606_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1606_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v_infoState_1573_; lean_object* v_env_1574_; lean_object* v_nextMacroScope_1575_; lean_object* v_ngen_1576_; lean_object* v_auxDeclNGen_1577_; lean_object* v_traceState_1578_; lean_object* v_cache_1579_; lean_object* v_messages_1580_; lean_object* v_snapshotTasks_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1605_; 
v___x_1572_ = lean_st_ref_take(v___y_1552_);
v_infoState_1573_ = lean_ctor_get(v___x_1572_, 7);
v_env_1574_ = lean_ctor_get(v___x_1572_, 0);
v_nextMacroScope_1575_ = lean_ctor_get(v___x_1572_, 1);
v_ngen_1576_ = lean_ctor_get(v___x_1572_, 2);
v_auxDeclNGen_1577_ = lean_ctor_get(v___x_1572_, 3);
v_traceState_1578_ = lean_ctor_get(v___x_1572_, 4);
v_cache_1579_ = lean_ctor_get(v___x_1572_, 5);
v_messages_1580_ = lean_ctor_get(v___x_1572_, 6);
v_snapshotTasks_1581_ = lean_ctor_get(v___x_1572_, 8);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1583_ = v___x_1572_;
v_isShared_1584_ = v_isSharedCheck_1605_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_snapshotTasks_1581_);
lean_inc(v_infoState_1573_);
lean_inc(v_messages_1580_);
lean_inc(v_cache_1579_);
lean_inc(v_traceState_1578_);
lean_inc(v_auxDeclNGen_1577_);
lean_inc(v_ngen_1576_);
lean_inc(v_nextMacroScope_1575_);
lean_inc(v_env_1574_);
lean_dec(v___x_1572_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1605_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
uint8_t v_enabled_1585_; lean_object* v_assignment_1586_; lean_object* v_lazyAssignment_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1603_; 
v_enabled_1585_ = lean_ctor_get_uint8(v_infoState_1573_, sizeof(void*)*3);
v_assignment_1586_ = lean_ctor_get(v_infoState_1573_, 0);
v_lazyAssignment_1587_ = lean_ctor_get(v_infoState_1573_, 1);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_infoState_1573_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; 
v_unused_1604_ = lean_ctor_get(v_infoState_1573_, 2);
lean_dec(v_unused_1604_);
v___x_1589_ = v_infoState_1573_;
v_isShared_1590_ = v_isSharedCheck_1603_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_lazyAssignment_1587_);
lean_inc(v_assignment_1586_);
lean_dec(v_infoState_1573_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1603_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1591_ = l_Lean_PersistentArray_push___redArg(v_a_1561_, v_a_1568_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 2, v___x_1591_);
v___x_1593_ = v___x_1589_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_assignment_1586_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_lazyAssignment_1587_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v___x_1591_);
lean_ctor_set_uint8(v_reuseFailAlloc_1602_, sizeof(void*)*3, v_enabled_1585_);
v___x_1593_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1595_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 7, v___x_1593_);
v___x_1595_ = v___x_1583_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_env_1574_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_nextMacroScope_1575_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_ngen_1576_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_auxDeclNGen_1577_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_traceState_1578_);
lean_ctor_set(v_reuseFailAlloc_1601_, 5, v_cache_1579_);
lean_ctor_set(v_reuseFailAlloc_1601_, 6, v_messages_1580_);
lean_ctor_set(v_reuseFailAlloc_1601_, 7, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1601_, 8, v_snapshotTasks_1581_);
v___x_1595_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1596_ = lean_st_ref_set(v___y_1552_, v___x_1595_);
lean_dec(v___y_1552_);
v___x_1597_ = lean_box(0);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1597_);
v___x_1599_ = v___x_1570_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v_a_1561_);
lean_dec(v___y_1552_);
v_a_1607_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1567_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1567_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0___boxed(lean_object* v___y_1615_, lean_object* v_mkInfoTree_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v_a_1624_, lean_object* v_a_x3f_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1615_, v_mkInfoTree_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v_a_1624_, v_a_x3f_1625_);
lean_dec(v_a_x3f_1625_);
return v_res_1627_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_unsigned_to_nat(32u);
v___x_1629_ = lean_mk_empty_array_with_capacity(v___x_1628_);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1631_ = ((size_t)5ULL);
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = lean_unsigned_to_nat(32u);
v___x_1634_ = lean_mk_empty_array_with_capacity(v___x_1633_);
v___x_1635_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0);
v___x_1636_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v___x_1634_);
lean_ctor_set(v___x_1636_, 2, v___x_1632_);
lean_ctor_set(v___x_1636_, 3, v___x_1632_);
lean_ctor_set_usize(v___x_1636_, 4, v___x_1631_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; lean_object* v_infoState_1640_; lean_object* v_trees_1641_; lean_object* v___x_1642_; lean_object* v_infoState_1643_; lean_object* v_env_1644_; lean_object* v_nextMacroScope_1645_; lean_object* v_ngen_1646_; lean_object* v_auxDeclNGen_1647_; lean_object* v_traceState_1648_; lean_object* v_cache_1649_; lean_object* v_messages_1650_; lean_object* v_snapshotTasks_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1672_; 
v___x_1639_ = lean_st_ref_get(v___y_1637_);
v_infoState_1640_ = lean_ctor_get(v___x_1639_, 7);
lean_inc_ref(v_infoState_1640_);
lean_dec(v___x_1639_);
v_trees_1641_ = lean_ctor_get(v_infoState_1640_, 2);
lean_inc_ref(v_trees_1641_);
lean_dec_ref(v_infoState_1640_);
v___x_1642_ = lean_st_ref_take(v___y_1637_);
v_infoState_1643_ = lean_ctor_get(v___x_1642_, 7);
v_env_1644_ = lean_ctor_get(v___x_1642_, 0);
v_nextMacroScope_1645_ = lean_ctor_get(v___x_1642_, 1);
v_ngen_1646_ = lean_ctor_get(v___x_1642_, 2);
v_auxDeclNGen_1647_ = lean_ctor_get(v___x_1642_, 3);
v_traceState_1648_ = lean_ctor_get(v___x_1642_, 4);
v_cache_1649_ = lean_ctor_get(v___x_1642_, 5);
v_messages_1650_ = lean_ctor_get(v___x_1642_, 6);
v_snapshotTasks_1651_ = lean_ctor_get(v___x_1642_, 8);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1653_ = v___x_1642_;
v_isShared_1654_ = v_isSharedCheck_1672_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_snapshotTasks_1651_);
lean_inc(v_infoState_1643_);
lean_inc(v_messages_1650_);
lean_inc(v_cache_1649_);
lean_inc(v_traceState_1648_);
lean_inc(v_auxDeclNGen_1647_);
lean_inc(v_ngen_1646_);
lean_inc(v_nextMacroScope_1645_);
lean_inc(v_env_1644_);
lean_dec(v___x_1642_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1672_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
uint8_t v_enabled_1655_; lean_object* v_assignment_1656_; lean_object* v_lazyAssignment_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1670_; 
v_enabled_1655_ = lean_ctor_get_uint8(v_infoState_1643_, sizeof(void*)*3);
v_assignment_1656_ = lean_ctor_get(v_infoState_1643_, 0);
v_lazyAssignment_1657_ = lean_ctor_get(v_infoState_1643_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_infoState_1643_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; 
v_unused_1671_ = lean_ctor_get(v_infoState_1643_, 2);
lean_dec(v_unused_1671_);
v___x_1659_ = v_infoState_1643_;
v_isShared_1660_ = v_isSharedCheck_1670_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_lazyAssignment_1657_);
lean_inc(v_assignment_1656_);
lean_dec(v_infoState_1643_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1670_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 2, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_assignment_1656_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_lazyAssignment_1657_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v___x_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*3, v_enabled_1655_);
v___x_1663_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 7, v___x_1663_);
v___x_1665_ = v___x_1653_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_env_1644_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_nextMacroScope_1645_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_ngen_1646_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v_auxDeclNGen_1647_);
lean_ctor_set(v_reuseFailAlloc_1668_, 4, v_traceState_1648_);
lean_ctor_set(v_reuseFailAlloc_1668_, 5, v_cache_1649_);
lean_ctor_set(v_reuseFailAlloc_1668_, 6, v_messages_1650_);
lean_ctor_set(v_reuseFailAlloc_1668_, 7, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1668_, 8, v_snapshotTasks_1651_);
v___x_1665_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_st_ref_set(v___y_1637_, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_trees_1641_);
return v___x_1667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_1673_);
lean_dec(v___y_1673_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(lean_object* v_x_1676_, lean_object* v_mkInfoTree_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; lean_object* v_infoState_1688_; uint8_t v_enabled_1689_; 
v___x_1687_ = lean_st_ref_get(v___y_1685_);
v_infoState_1688_ = lean_ctor_get(v___x_1687_, 7);
lean_inc_ref(v_infoState_1688_);
lean_dec(v___x_1687_);
v_enabled_1689_ = lean_ctor_get_uint8(v_infoState_1688_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1688_);
if (v_enabled_1689_ == 0)
{
lean_object* v___x_1690_; 
lean_dec_ref(v_mkInfoTree_1677_);
v___x_1690_ = lean_apply_9(v_x_1676_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, lean_box(0));
return v___x_1690_;
}
else
{
lean_object* v___x_1691_; lean_object* v_a_1692_; lean_object* v_r_1693_; 
v___x_1691_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_1685_);
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref(v___x_1691_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
v_r_1693_ = lean_apply_9(v_x_1676_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, lean_box(0));
if (lean_obj_tag(v_r_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1718_; 
v_a_1694_ = lean_ctor_get(v_r_1693_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_r_1693_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1696_ = v_r_1693_;
v_isShared_1697_ = v_isSharedCheck_1718_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v_r_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1718_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
lean_inc(v_a_1694_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 1);
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1685_, v_mkInfoTree_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v_a_1692_, v___x_1699_);
lean_dec_ref(v___x_1699_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; 
v_unused_1708_ = lean_ctor_get(v___x_1700_, 0);
lean_dec(v_unused_1708_);
v___x_1702_ = v___x_1700_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_dec(v___x_1700_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v_a_1694_);
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1694_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_a_1694_);
v_a_1709_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1700_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1700_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_a_1719_ = lean_ctor_get(v_r_1693_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v_r_1693_);
v___x_1720_ = lean_box(0);
v___x_1721_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1685_, v_mkInfoTree_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v_a_1692_, v___x_1720_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v___x_1721_, 0);
lean_dec(v_unused_1729_);
v___x_1723_ = v___x_1721_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_dec(v___x_1721_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 1);
lean_ctor_set(v___x_1723_, 0, v_a_1719_);
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1719_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_a_1719_);
v_a_1730_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1721_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1721_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___boxed(lean_object* v_x_1738_, lean_object* v_mkInfoTree_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v_x_1738_, v_mkInfoTree_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(lean_object* v___x_1759_, uint8_t v___x_1760_, lean_object* v___x_1761_, lean_object* v_x_1762_, uint8_t v___y_1763_, lean_object* v___x_1764_, lean_object* v___x_1765_, lean_object* v___f_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_fileName_1776_; lean_object* v_fileMap_1777_; lean_object* v_options_1778_; lean_object* v_currRecDepth_1779_; lean_object* v_maxRecDepth_1780_; lean_object* v_ref_1781_; lean_object* v_currNamespace_1782_; lean_object* v_openDecls_1783_; lean_object* v_initHeartbeats_1784_; lean_object* v_maxHeartbeats_1785_; lean_object* v_quotContext_1786_; lean_object* v_currMacroScope_1787_; uint8_t v_diag_1788_; lean_object* v_cancelTk_x3f_1789_; uint8_t v_suppressElabErrors_1790_; lean_object* v_inheritedTraceOptions_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1809_; 
v_fileName_1776_ = lean_ctor_get(v___y_1773_, 0);
v_fileMap_1777_ = lean_ctor_get(v___y_1773_, 1);
v_options_1778_ = lean_ctor_get(v___y_1773_, 2);
v_currRecDepth_1779_ = lean_ctor_get(v___y_1773_, 3);
v_maxRecDepth_1780_ = lean_ctor_get(v___y_1773_, 4);
v_ref_1781_ = lean_ctor_get(v___y_1773_, 5);
v_currNamespace_1782_ = lean_ctor_get(v___y_1773_, 6);
v_openDecls_1783_ = lean_ctor_get(v___y_1773_, 7);
v_initHeartbeats_1784_ = lean_ctor_get(v___y_1773_, 8);
v_maxHeartbeats_1785_ = lean_ctor_get(v___y_1773_, 9);
v_quotContext_1786_ = lean_ctor_get(v___y_1773_, 10);
v_currMacroScope_1787_ = lean_ctor_get(v___y_1773_, 11);
v_diag_1788_ = lean_ctor_get_uint8(v___y_1773_, sizeof(void*)*14);
v_cancelTk_x3f_1789_ = lean_ctor_get(v___y_1773_, 12);
v_suppressElabErrors_1790_ = lean_ctor_get_uint8(v___y_1773_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1791_ = lean_ctor_get(v___y_1773_, 13);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___y_1773_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1793_ = v___y_1773_;
v_isShared_1794_ = v_isSharedCheck_1809_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_inheritedTraceOptions_1791_);
lean_inc(v_cancelTk_x3f_1789_);
lean_inc(v_currMacroScope_1787_);
lean_inc(v_quotContext_1786_);
lean_inc(v_maxHeartbeats_1785_);
lean_inc(v_initHeartbeats_1784_);
lean_inc(v_openDecls_1783_);
lean_inc(v_currNamespace_1782_);
lean_inc(v_ref_1781_);
lean_inc(v_maxRecDepth_1780_);
lean_inc(v_currRecDepth_1779_);
lean_inc(v_options_1778_);
lean_inc(v_fileMap_1777_);
lean_inc(v_fileName_1776_);
lean_dec(v___y_1773_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1809_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v_ref_1795_; lean_object* v___x_1797_; 
v_ref_1795_ = l_Lean_replaceRef(v___x_1759_, v_ref_1781_);
lean_dec(v_ref_1781_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 5, v_ref_1795_);
v___x_1797_ = v___x_1793_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_fileName_1776_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_fileMap_1777_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_options_1778_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_currRecDepth_1779_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_maxRecDepth_1780_);
lean_ctor_set(v_reuseFailAlloc_1808_, 5, v_ref_1795_);
lean_ctor_set(v_reuseFailAlloc_1808_, 6, v_currNamespace_1782_);
lean_ctor_set(v_reuseFailAlloc_1808_, 7, v_openDecls_1783_);
lean_ctor_set(v_reuseFailAlloc_1808_, 8, v_initHeartbeats_1784_);
lean_ctor_set(v_reuseFailAlloc_1808_, 9, v_maxHeartbeats_1785_);
lean_ctor_set(v_reuseFailAlloc_1808_, 10, v_quotContext_1786_);
lean_ctor_set(v_reuseFailAlloc_1808_, 11, v_currMacroScope_1787_);
lean_ctor_set(v_reuseFailAlloc_1808_, 12, v_cancelTk_x3f_1789_);
lean_ctor_set(v_reuseFailAlloc_1808_, 13, v_inheritedTraceOptions_1791_);
lean_ctor_set_uint8(v_reuseFailAlloc_1808_, sizeof(void*)*14, v_diag_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1808_, sizeof(void*)*14 + 1, v_suppressElabErrors_1790_);
v___x_1797_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
if (v___x_1760_ == 0)
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4));
lean_inc(v___x_1761_);
v___x_1799_ = l_Lean_Syntax_isOfKind(v___x_1761_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec_ref(v___f_1766_);
v___x_1800_ = lean_box(v___y_1763_);
v___x_1801_ = lean_apply_11(v_x_1762_, v___x_1800_, v___x_1761_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___x_1797_, v___y_1774_, lean_box(0));
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = l_Lean_Syntax_getArg(v___x_1761_, v___x_1764_);
lean_inc(v___x_1802_);
v___x_1803_ = l_Lean_Syntax_isOfKind(v___x_1802_, v___x_1765_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v___x_1802_);
lean_dec_ref(v___f_1766_);
v___x_1804_ = lean_box(v___y_1763_);
v___x_1805_ = lean_apply_11(v_x_1762_, v___x_1804_, v___x_1761_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___x_1797_, v___y_1774_, lean_box(0));
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; 
lean_dec_ref(v_x_1762_);
lean_dec(v___x_1761_);
v___x_1806_ = lean_apply_10(v___f_1766_, v___x_1802_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___x_1797_, v___y_1774_, lean_box(0));
return v___x_1806_;
}
}
}
else
{
lean_object* v___x_1807_; 
lean_dec_ref(v_x_1762_);
v___x_1807_ = lean_apply_10(v___f_1766_, v___x_1761_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___x_1797_, v___y_1774_, lean_box(0));
return v___x_1807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_1810_ = _args[0];
lean_object* v___x_1811_ = _args[1];
lean_object* v___x_1812_ = _args[2];
lean_object* v_x_1813_ = _args[3];
lean_object* v___y_1814_ = _args[4];
lean_object* v___x_1815_ = _args[5];
lean_object* v___x_1816_ = _args[6];
lean_object* v___f_1817_ = _args[7];
lean_object* v___y_1818_ = _args[8];
lean_object* v___y_1819_ = _args[9];
lean_object* v___y_1820_ = _args[10];
lean_object* v___y_1821_ = _args[11];
lean_object* v___y_1822_ = _args[12];
lean_object* v___y_1823_ = _args[13];
lean_object* v___y_1824_ = _args[14];
lean_object* v___y_1825_ = _args[15];
lean_object* v___y_1826_ = _args[16];
_start:
{
uint8_t v___x_18301__boxed_1827_; uint8_t v___y_18303__boxed_1828_; lean_object* v_res_1829_; 
v___x_18301__boxed_1827_ = lean_unbox(v___x_1811_);
v___y_18303__boxed_1828_ = lean_unbox(v___y_1814_);
v_res_1829_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(v___x_1810_, v___x_18301__boxed_1827_, v___x_1812_, v_x_1813_, v___y_18303__boxed_1828_, v___x_1815_, v___x_1816_, v___f_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___x_1816_);
lean_dec(v___x_1815_);
lean_dec(v___x_1810_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(lean_object* v_a_1830_, lean_object* v_trees_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_apply_9(v_a_1830_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, lean_box(0));
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1850_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1846_, 0, v_a_1842_);
lean_ctor_set(v___x_1846_, 1, v_trees_1831_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1846_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v_trees_1831_);
v_a_1851_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1841_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1841_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object* v_a_1859_, lean_object* v_trees_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(v_a_1859_, v_trees_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(lean_object* v_id_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Elab_Term_isLocalIdent_x3f(v_id_1871_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object* v_id_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(v_id_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec(v___y_1888_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
return v_res_1892_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0));
v___x_1895_ = l_Lean_stringToMessageData(v___x_1894_);
return v___x_1895_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2));
v___x_1898_ = l_Lean_stringToMessageData(v___x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(lean_object* v_x_1899_, uint8_t v___y_1900_, lean_object* v___x_1901_, lean_object* v___x_1902_, lean_object* v_id_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___f_1913_; lean_object* v___x_1914_; 
lean_inc(v_id_1903_);
v___f_1913_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1913_, 0, v_id_1903_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
v___x_1914_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1913_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref(v___x_1914_);
if (lean_obj_tag(v_a_1915_) == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_1905_, v___y_1907_, v___y_1909_, v___y_1911_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v___x_1916_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v_id_1903_);
v___x_1918_ = l_Lean_realizeGlobalConstNoOverload(v_id_1903_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; 
lean_dec(v_a_1917_);
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1918_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v_a_1919_);
v___x_1920_ = l_Lean_Meta_getEqnsFor_x3f(v_a_1919_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1920_);
if (lean_obj_tag(v_a_1921_) == 1)
{
lean_object* v_val_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v___x_1902_);
v_val_1922_ = lean_ctor_get(v_a_1921_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_a_1921_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1924_ = v_a_1921_;
v_isShared_1925_ = v_isSharedCheck_1966_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_val_1922_);
lean_dec(v_a_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1966_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
uint8_t v___x_1926_; lean_object* v___y_1928_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1926_ = 0;
v___x_1955_ = lean_array_get_size(v_val_1922_);
v___x_1956_ = lean_nat_dec_eq(v___x_1955_, v___x_1901_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1957_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1);
v___x_1958_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_a_1919_);
v___x_1959_ = l_Lean_Name_str___override(v_a_1919_, v___x_1958_);
v___x_1960_ = l_Lean_MessageData_ofName(v___x_1959_);
v___x_1961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1957_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = l_Lean_MessageData_hint_x27(v___x_1963_);
v___y_1928_ = v___x_1964_;
goto v___jp_1927_;
}
else
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3);
v___y_1928_ = v___x_1965_;
goto v___jp_1927_;
}
v___jp_1927_:
{
lean_object* v___x_1929_; 
lean_inc_ref(v___y_1910_);
lean_inc(v_a_1919_);
v___x_1929_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_1919_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v_lctx_1931_; lean_object* v___x_1933_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___x_1929_);
v_lctx_1931_ = lean_ctor_get(v___y_1908_, 2);
lean_inc_ref(v_lctx_1931_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v_lctx_1931_);
v___x_1933_ = v___x_1924_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_lctx_1931_);
v___x_1933_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_box(0);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v_id_1903_);
v___x_1935_ = l_Lean_Elab_Term_addTermInfo(v_id_1903_, v_a_1930_, v_a_1915_, v___x_1933_, v___x_1934_, v___x_1926_, v___x_1926_, v___x_1926_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec_ref(v___x_1935_);
v___x_1936_ = lean_array_to_list(v_val_1922_);
v___x_1937_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(v_x_1899_, v___y_1900_, v_id_1903_, v_a_1919_, v___y_1928_, v___x_1936_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v_id_1903_);
return v___x_1937_;
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v___y_1928_);
lean_dec(v_val_1922_);
lean_dec(v_a_1919_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v_id_1903_);
lean_dec_ref(v_x_1899_);
v_a_1938_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1935_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1935_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v___y_1928_);
lean_del_object(v___x_1924_);
lean_dec(v_val_1922_);
lean_dec(v_a_1919_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v_id_1903_);
lean_dec_ref(v_x_1899_);
v_a_1947_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1929_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1929_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_dec(v_a_1921_);
lean_dec(v_a_1919_);
lean_dec(v_id_1903_);
v___x_1967_ = lean_box(v___y_1900_);
v___x_1968_ = lean_apply_11(v_x_1899_, v___x_1967_, v___x_1902_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, lean_box(0));
return v___x_1968_;
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v_a_1919_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v_id_1903_);
lean_dec(v___x_1902_);
lean_dec_ref(v_x_1899_);
v_a_1969_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1920_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1920_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_id_1903_);
v_a_1977_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1979_ = v___x_1918_;
v_isShared_1980_ = v_isSharedCheck_1991_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1918_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1991_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
uint8_t v___y_1982_; uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_Exception_isInterrupt(v_a_1977_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; 
lean_inc(v_a_1977_);
v___x_1990_ = l_Lean_Exception_isRuntime(v_a_1977_);
v___y_1982_ = v___x_1990_;
goto v___jp_1981_;
}
else
{
v___y_1982_ = v___x_1989_;
goto v___jp_1981_;
}
v___jp_1981_:
{
if (v___y_1982_ == 0)
{
lean_object* v___x_1983_; 
lean_del_object(v___x_1979_);
lean_dec(v_a_1977_);
v___x_1983_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1917_, v___y_1982_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec_ref(v___x_1983_);
v___x_1984_ = lean_box(v___y_1900_);
v___x_1985_ = lean_apply_11(v_x_1899_, v___x_1984_, v___x_1902_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, lean_box(0));
return v___x_1985_;
}
else
{
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___x_1902_);
lean_dec_ref(v_x_1899_);
return v___x_1983_;
}
}
else
{
lean_object* v___x_1987_; 
lean_dec(v_a_1917_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___x_1902_);
lean_dec_ref(v_x_1899_);
if (v_isShared_1980_ == 0)
{
v___x_1987_ = v___x_1979_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1977_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v_id_1903_);
lean_dec(v___x_1902_);
lean_dec_ref(v_x_1899_);
v_a_1992_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1916_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1916_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec_ref(v_a_1915_);
lean_dec(v_id_1903_);
v___x_2000_ = lean_box(v___y_1900_);
v___x_2001_ = lean_apply_11(v_x_1899_, v___x_2000_, v___x_1902_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, lean_box(0));
return v___x_2001_;
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v_id_1903_);
lean_dec(v___x_1902_);
lean_dec_ref(v_x_1899_);
v_a_2002_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1914_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1914_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object* v_x_2010_, lean_object* v___y_2011_, lean_object* v___x_2012_, lean_object* v___x_2013_, lean_object* v_id_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v___y_18501__boxed_2024_; lean_object* v_res_2025_; 
v___y_18501__boxed_2024_ = lean_unbox(v___y_2011_);
v_res_2025_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(v_x_2010_, v___y_18501__boxed_2024_, v___x_2012_, v___x_2013_, v_id_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___x_2012_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(lean_object* v_upperBound_2032_, lean_object* v_rules_2033_, lean_object* v_x_2034_, lean_object* v_a_2035_, lean_object* v_b_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_nat_dec_lt(v_a_2035_, v_upperBound_2032_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; 
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v_a_2035_);
lean_dec_ref(v_x_2034_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_b_2036_);
return v___x_2047_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___y_2056_; uint8_t v___y_2057_; lean_object* v___y_2081_; lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2048_ = lean_unsigned_to_nat(2u);
v___x_2049_ = lean_box(0);
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = lean_box(0);
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_nat_mul(v_a_2035_, v___x_2048_);
v___x_2054_ = lean_array_get_borrowed(v___x_2049_, v_rules_2033_, v___x_2053_);
v___x_2091_ = lean_nat_add(v___x_2053_, v___x_2050_);
lean_dec(v___x_2053_);
v___x_2092_ = lean_array_get_size(v_rules_2033_);
v___x_2093_ = lean_nat_dec_lt(v___x_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_dec(v___x_2091_);
v___y_2081_ = v___x_2049_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_array_fget_borrowed(v_rules_2033_, v___x_2091_);
lean_dec(v___x_2091_);
lean_inc(v___x_2094_);
v___y_2081_ = v___x_2094_;
goto v___jp_2080_;
}
v___jp_2055_:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___y_2056_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___f_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___f_2068_; lean_object* v___x_2069_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v___x_2058_);
v___f_2060_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2060_, 0, v_a_2059_);
v___x_2061_ = l_Lean_Syntax_getArg(v___x_2054_, v___x_2050_);
v___x_2062_ = lean_box(v___y_2057_);
lean_inc(v___x_2061_);
lean_inc_ref(v_x_2034_);
v___f_2063_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2063_, 0, v_x_2034_);
lean_closure_set(v___f_2063_, 1, v___x_2062_);
lean_closure_set(v___f_2063_, 2, v___x_2050_);
lean_closure_set(v___f_2063_, 3, v___x_2061_);
v___x_2064_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1));
lean_inc(v___x_2061_);
v___x_2065_ = l_Lean_Syntax_isOfKind(v___x_2061_, v___x_2064_);
v___x_2066_ = lean_box(v___x_2065_);
v___x_2067_ = lean_box(v___y_2057_);
lean_inc_ref(v_x_2034_);
lean_inc(v___x_2054_);
v___f_2068_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed), 17, 8);
lean_closure_set(v___f_2068_, 0, v___x_2054_);
lean_closure_set(v___f_2068_, 1, v___x_2066_);
lean_closure_set(v___f_2068_, 2, v___x_2061_);
lean_closure_set(v___f_2068_, 3, v_x_2034_);
lean_closure_set(v___f_2068_, 4, v___x_2067_);
lean_closure_set(v___f_2068_, 5, v___x_2050_);
lean_closure_set(v___f_2068_, 6, v___x_2064_);
lean_closure_set(v___f_2068_, 7, v___f_2063_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
v___x_2069_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_2068_, v___f_2060_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v___x_2070_; 
lean_dec_ref(v___x_2069_);
v___x_2070_ = lean_nat_add(v_a_2035_, v___x_2050_);
lean_dec(v_a_2035_);
v_a_2035_ = v___x_2070_;
v_b_2036_ = v___x_2051_;
goto _start;
}
else
{
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v_a_2035_);
lean_dec_ref(v_x_2034_);
return v___x_2069_;
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v_a_2035_);
lean_dec_ref(v_x_2034_);
v_a_2072_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2058_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2058_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
v___jp_2080_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2082_ = lean_mk_empty_array_with_capacity(v___x_2048_);
lean_inc(v___x_2054_);
v___x_2083_ = lean_array_push(v___x_2082_, v___x_2054_);
v___x_2084_ = lean_array_push(v___x_2083_, v___y_2081_);
v___x_2085_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3));
v___x_2086_ = lean_box(2);
v___x_2087_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___x_2085_);
lean_ctor_set(v___x_2087_, 2, v___x_2084_);
v___x_2088_ = l_Lean_Syntax_getArg(v___x_2054_, v___x_2052_);
v___x_2089_ = l_Lean_Syntax_isNone(v___x_2088_);
lean_dec(v___x_2088_);
if (v___x_2089_ == 0)
{
v___y_2056_ = v___x_2087_;
v___y_2057_ = v___x_2046_;
goto v___jp_2055_;
}
else
{
uint8_t v___x_2090_; 
v___x_2090_ = 0;
v___y_2056_ = v___x_2087_;
v___y_2057_ = v___x_2090_;
goto v___jp_2055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___boxed(lean_object* v_upperBound_2095_, lean_object* v_rules_2096_, lean_object* v_x_2097_, lean_object* v_a_2098_, lean_object* v_b_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v_upperBound_2095_, v_rules_2096_, v_x_2097_, v_a_2098_, v_b_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec_ref(v_rules_2096_);
lean_dec(v_upperBound_2095_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object* v_token_2112_, lean_object* v_rwRulesSeqStx_2113_, lean_object* v_x_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v___x_2124_; lean_object* v_lbrak_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2124_ = lean_unsigned_to_nat(0u);
v_lbrak_2125_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2113_, v___x_2124_);
v___x_2126_ = lean_unsigned_to_nat(2u);
v___x_2127_ = lean_mk_empty_array_with_capacity(v___x_2126_);
v___x_2128_ = lean_array_push(v___x_2127_, v_token_2112_);
v___x_2129_ = lean_array_push(v___x_2128_, v_lbrak_2125_);
v___x_2130_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3));
v___x_2131_ = lean_box(2);
v___x_2132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___x_2130_);
lean_ctor_set(v___x_2132_, 2, v___x_2129_);
v___x_2133_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2132_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___f_2135_; lean_object* v___x_2136_; lean_object* v___f_2137_; lean_object* v___x_2138_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref(v___x_2133_);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2135_, 0, v_a_2134_);
v___x_2136_ = lean_box(0);
v___f_2137_ = ((lean_object*)(l_Lean_Elab_Tactic_withRWRulesSeq___closed__0));
lean_inc(v_a_2122_);
lean_inc_ref(v_a_2121_);
lean_inc(v_a_2120_);
lean_inc_ref(v_a_2119_);
lean_inc(v_a_2118_);
lean_inc_ref(v_a_2117_);
lean_inc(v_a_2116_);
lean_inc_ref(v_a_2115_);
v___x_2138_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_2137_, v___f_2135_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v_rules_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec_ref(v___x_2138_);
v___x_2139_ = lean_unsigned_to_nat(1u);
v___x_2140_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2113_, v___x_2139_);
v_rules_2141_ = l_Lean_Syntax_getArgs(v___x_2140_);
lean_dec(v___x_2140_);
v___x_2142_ = lean_array_get_size(v_rules_2141_);
v___x_2143_ = lean_nat_add(v___x_2142_, v___x_2139_);
v___x_2144_ = lean_nat_shiftr(v___x_2143_, v___x_2139_);
lean_dec(v___x_2143_);
v___x_2145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v___x_2144_, v_rules_2141_, v_x_2114_, v___x_2124_, v___x_2136_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
lean_dec_ref(v_rules_2141_);
lean_dec(v___x_2144_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v___x_2145_, 0);
lean_dec(v_unused_2153_);
v___x_2147_ = v___x_2145_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_dec(v___x_2145_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2136_);
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2136_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
else
{
return v___x_2145_;
}
}
else
{
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec_ref(v_x_2114_);
return v___x_2138_;
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec_ref(v_x_2114_);
v_a_2154_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2133_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2133_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object* v_token_2162_, lean_object* v_rwRulesSeqStx_2163_, lean_object* v_x_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_Elab_Tactic_withRWRulesSeq(v_token_2162_, v_rwRulesSeqStx_2163_, v_x_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
lean_dec(v_rwRulesSeqStx_2163_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_2182_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___boxed(lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(lean_object* v_00_u03b1_2195_, lean_object* v_x_2196_, lean_object* v_mkInfoTree_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v_x_2196_, v_mkInfoTree_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___boxed(lean_object* v_00_u03b1_2208_, lean_object* v_x_2209_, lean_object* v_mkInfoTree_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(v_00_u03b1_2208_, v_x_2209_, v_mkInfoTree_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(lean_object* v_upperBound_2221_, lean_object* v_rules_2222_, lean_object* v_x_2223_, lean_object* v_inst_2224_, lean_object* v_R_2225_, lean_object* v_a_2226_, lean_object* v_b_2227_, lean_object* v_c_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v_upperBound_2221_, v_rules_2222_, v_x_2223_, v_a_2226_, v_b_2227_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2239_ = _args[0];
lean_object* v_rules_2240_ = _args[1];
lean_object* v_x_2241_ = _args[2];
lean_object* v_inst_2242_ = _args[3];
lean_object* v_R_2243_ = _args[4];
lean_object* v_a_2244_ = _args[5];
lean_object* v_b_2245_ = _args[6];
lean_object* v_c_2246_ = _args[7];
lean_object* v___y_2247_ = _args[8];
lean_object* v___y_2248_ = _args[9];
lean_object* v___y_2249_ = _args[10];
lean_object* v___y_2250_ = _args[11];
lean_object* v___y_2251_ = _args[12];
lean_object* v___y_2252_ = _args[13];
lean_object* v___y_2253_ = _args[14];
lean_object* v___y_2254_ = _args[15];
lean_object* v___y_2255_ = _args[16];
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(v_upperBound_2239_, v_rules_2240_, v_x_2241_, v_inst_2242_, v_R_2243_, v_a_2244_, v_b_2245_, v_c_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec_ref(v_rules_2240_);
lean_dec(v_upperBound_2239_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(lean_object* v_e_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v___x_2271_; uint8_t v___x_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; 
v___x_2271_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_));
v___x_2272_ = 0;
v___x_2273_ = 1;
v___x_2274_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_2271_, v_e_2265_, v___x_2272_, v___x_2273_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3____boxed(lean_object* v_e_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(v_e_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(lean_object* v_e_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(v_e_2282_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3____boxed(lean_object* v_e_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(v_e_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
return v_res_2299_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2300_; double v___x_2301_; 
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = lean_float_of_nat(v___x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg(lean_object* v_cls_2304_, lean_object* v_msg_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_ref_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2357_; 
v_ref_2311_ = lean_ctor_get(v___y_2308_, 5);
v___x_2312_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3_spec__8(v_msg_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2357_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2357_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v_traceState_2318_; lean_object* v_env_2319_; lean_object* v_nextMacroScope_2320_; lean_object* v_ngen_2321_; lean_object* v_auxDeclNGen_2322_; lean_object* v_cache_2323_; lean_object* v_messages_2324_; lean_object* v_infoState_2325_; lean_object* v_snapshotTasks_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2356_; 
v___x_2317_ = lean_st_ref_take(v___y_2309_);
v_traceState_2318_ = lean_ctor_get(v___x_2317_, 4);
v_env_2319_ = lean_ctor_get(v___x_2317_, 0);
v_nextMacroScope_2320_ = lean_ctor_get(v___x_2317_, 1);
v_ngen_2321_ = lean_ctor_get(v___x_2317_, 2);
v_auxDeclNGen_2322_ = lean_ctor_get(v___x_2317_, 3);
v_cache_2323_ = lean_ctor_get(v___x_2317_, 5);
v_messages_2324_ = lean_ctor_get(v___x_2317_, 6);
v_infoState_2325_ = lean_ctor_get(v___x_2317_, 7);
v_snapshotTasks_2326_ = lean_ctor_get(v___x_2317_, 8);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2328_ = v___x_2317_;
v_isShared_2329_ = v_isSharedCheck_2356_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_snapshotTasks_2326_);
lean_inc(v_infoState_2325_);
lean_inc(v_messages_2324_);
lean_inc(v_cache_2323_);
lean_inc(v_traceState_2318_);
lean_inc(v_auxDeclNGen_2322_);
lean_inc(v_ngen_2321_);
lean_inc(v_nextMacroScope_2320_);
lean_inc(v_env_2319_);
lean_dec(v___x_2317_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2356_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
uint64_t v_tid_2330_; lean_object* v_traces_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2355_; 
v_tid_2330_ = lean_ctor_get_uint64(v_traceState_2318_, sizeof(void*)*1);
v_traces_2331_ = lean_ctor_get(v_traceState_2318_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_traceState_2318_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2333_ = v_traceState_2318_;
v_isShared_2334_ = v_isSharedCheck_2355_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_traces_2331_);
lean_dec(v_traceState_2318_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2355_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; double v___x_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2335_ = lean_box(0);
v___x_2336_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_2337_ = 0;
v___x_2338_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2));
v___x_2339_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2339_, 0, v_cls_2304_);
lean_ctor_set(v___x_2339_, 1, v___x_2335_);
lean_ctor_set(v___x_2339_, 2, v___x_2338_);
lean_ctor_set_float(v___x_2339_, sizeof(void*)*3, v___x_2336_);
lean_ctor_set_float(v___x_2339_, sizeof(void*)*3 + 8, v___x_2336_);
lean_ctor_set_uint8(v___x_2339_, sizeof(void*)*3 + 16, v___x_2337_);
v___x_2340_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_2341_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set(v___x_2341_, 1, v_a_2313_);
lean_ctor_set(v___x_2341_, 2, v___x_2340_);
lean_inc(v_ref_2311_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v_ref_2311_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = l_Lean_PersistentArray_push___redArg(v_traces_2331_, v___x_2342_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2343_);
v___x_2345_ = v___x_2333_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2343_);
lean_ctor_set_uint64(v_reuseFailAlloc_2354_, sizeof(void*)*1, v_tid_2330_);
v___x_2345_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2347_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 4, v___x_2345_);
v___x_2347_ = v___x_2328_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_env_2319_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_nextMacroScope_2320_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v_ngen_2321_);
lean_ctor_set(v_reuseFailAlloc_2353_, 3, v_auxDeclNGen_2322_);
lean_ctor_set(v_reuseFailAlloc_2353_, 4, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2353_, 5, v_cache_2323_);
lean_ctor_set(v_reuseFailAlloc_2353_, 6, v_messages_2324_);
lean_ctor_set(v_reuseFailAlloc_2353_, 7, v_infoState_2325_);
lean_ctor_set(v_reuseFailAlloc_2353_, 8, v_snapshotTasks_2326_);
v___x_2347_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2348_ = lean_st_ref_set(v___y_2309_, v___x_2347_);
v___x_2349_ = lean_box(0);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2349_);
v___x_2351_ = v___x_2315_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_cls_2358_, lean_object* v_msg_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg(v_cls_2358_, v_msg_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2365_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object* v_keys_2366_, lean_object* v_i_2367_, lean_object* v_k_2368_){
_start:
{
lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2369_ = lean_array_get_size(v_keys_2366_);
v___x_2370_ = lean_nat_dec_lt(v_i_2367_, v___x_2369_);
if (v___x_2370_ == 0)
{
lean_dec(v_i_2367_);
return v___x_2370_;
}
else
{
lean_object* v_k_x27_2371_; uint8_t v___x_2372_; 
v_k_x27_2371_ = lean_array_fget_borrowed(v_keys_2366_, v_i_2367_);
v___x_2372_ = l_Lean_instBEqExtraModUse_beq(v_k_2368_, v_k_x27_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_nat_add(v_i_2367_, v___x_2373_);
lean_dec(v_i_2367_);
v_i_2367_ = v___x_2374_;
goto _start;
}
else
{
lean_dec(v_i_2367_);
return v___x_2372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_keys_2376_, lean_object* v_i_2377_, lean_object* v_k_2378_){
_start:
{
uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_res_2379_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_2376_, v_i_2377_, v_k_2378_);
lean_dec_ref(v_k_2378_);
lean_dec_ref(v_keys_2376_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_2381_, size_t v_x_2382_, lean_object* v_x_2383_){
_start:
{
if (lean_obj_tag(v_x_2381_) == 0)
{
lean_object* v_es_2384_; lean_object* v___x_2385_; size_t v___x_2386_; size_t v___x_2387_; size_t v___x_2388_; lean_object* v_j_2389_; lean_object* v___x_2390_; 
v_es_2384_ = lean_ctor_get(v_x_2381_, 0);
lean_inc_ref(v_es_2384_);
lean_dec_ref(v_x_2381_);
v___x_2385_ = lean_box(2);
v___x_2386_ = ((size_t)5ULL);
v___x_2387_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_2388_ = lean_usize_land(v_x_2382_, v___x_2387_);
v_j_2389_ = lean_usize_to_nat(v___x_2388_);
v___x_2390_ = lean_array_get(v___x_2385_, v_es_2384_, v_j_2389_);
lean_dec(v_j_2389_);
lean_dec_ref(v_es_2384_);
switch(lean_obj_tag(v___x_2390_))
{
case 0:
{
lean_object* v_key_2391_; uint8_t v___x_2392_; 
v_key_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_key_2391_);
lean_dec_ref(v___x_2390_);
v___x_2392_ = l_Lean_instBEqExtraModUse_beq(v_x_2383_, v_key_2391_);
lean_dec(v_key_2391_);
return v___x_2392_;
}
case 1:
{
lean_object* v_node_2393_; size_t v___x_2394_; 
v_node_2393_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_node_2393_);
lean_dec_ref(v___x_2390_);
v___x_2394_ = lean_usize_shift_right(v_x_2382_, v___x_2386_);
v_x_2381_ = v_node_2393_;
v_x_2382_ = v___x_2394_;
goto _start;
}
default: 
{
uint8_t v___x_2396_; 
v___x_2396_ = 0;
return v___x_2396_;
}
}
}
else
{
lean_object* v_ks_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_ks_2397_ = lean_ctor_get(v_x_2381_, 0);
lean_inc_ref(v_ks_2397_);
lean_dec_ref(v_x_2381_);
v___x_2398_ = lean_unsigned_to_nat(0u);
v___x_2399_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_2397_, v___x_2398_, v_x_2383_);
lean_dec_ref(v_ks_2397_);
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_){
_start:
{
size_t v_x_11819__boxed_2403_; uint8_t v_res_2404_; lean_object* v_r_2405_; 
v_x_11819__boxed_2403_ = lean_unbox_usize(v_x_2401_);
lean_dec(v_x_2401_);
v_res_2404_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2400_, v_x_11819__boxed_2403_, v_x_2402_);
lean_dec_ref(v_x_2402_);
v_r_2405_ = lean_box(v_res_2404_);
return v_r_2405_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
uint64_t v___x_2408_; size_t v___x_2409_; uint8_t v___x_2410_; 
v___x_2408_ = l_Lean_instHashableExtraModUse_hash(v_x_2407_);
v___x_2409_ = lean_uint64_to_usize(v___x_2408_);
v___x_2410_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2406_, v___x_2409_, v_x_2407_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2411_, lean_object* v_x_2412_){
_start:
{
uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_res_2413_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg(v_x_2411_, v_x_2412_);
lean_dec_ref(v_x_2412_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_options_2421_; uint8_t v_hasTrace_2422_; 
v_options_2421_ = lean_ctor_get(v___y_2419_, 2);
v_hasTrace_2422_ = lean_ctor_get_uint8(v_options_2421_, sizeof(void*)*1);
if (v_hasTrace_2422_ == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_dec(v_cls_2418_);
v___x_2423_ = lean_box(v_hasTrace_2422_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
else
{
lean_object* v_inheritedTraceOptions_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_inheritedTraceOptions_2425_ = lean_ctor_get(v___y_2419_, 13);
v___x_2426_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_2427_ = l_Lean_Name_append(v___x_2426_, v_cls_2418_);
v___x_2428_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2425_, v_options_2421_, v___x_2427_);
lean_dec(v___x_2427_);
v___x_2429_ = lean_box(v___x_2428_);
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
return v___x_2430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg(v_cls_2431_, v___y_2432_);
lean_dec_ref(v___y_2432_);
return v_res_2434_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__1));
v___x_2438_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__0));
v___x_2439_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2438_, v___x_2437_);
return v___x_2439_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2440_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__3);
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
return v___x_2444_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4);
v___x_2446_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
lean_ctor_set(v___x_2446_, 2, v___x_2445_);
lean_ctor_set(v___x_2446_, 3, v___x_2445_);
lean_ctor_set(v___x_2446_, 4, v___x_2445_);
lean_ctor_set(v___x_2446_, 5, v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__9));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__11));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__13));
v___x_2458_ = l_Lean_stringToMessageData(v___x_2457_);
return v___x_2458_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__15));
v___x_2461_ = l_Lean_stringToMessageData(v___x_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0(lean_object* v_mod_2466_, uint8_t v_isMeta_2467_, lean_object* v_hint_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; lean_object* v_env_2477_; uint8_t v_isExporting_2478_; lean_object* v___x_2479_; lean_object* v_env_2480_; lean_object* v___x_2481_; lean_object* v_entry_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2476_ = lean_st_ref_get(v___y_2474_);
v_env_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc_ref(v_env_2477_);
lean_dec(v___x_2476_);
v_isExporting_2478_ = lean_ctor_get_uint8(v_env_2477_, sizeof(void*)*8);
lean_dec_ref(v_env_2477_);
v___x_2479_ = lean_st_ref_get(v___y_2474_);
v_env_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc_ref(v_env_2480_);
lean_dec(v___x_2479_);
v___x_2481_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_2466_);
v_entry_2482_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2482_, 0, v_mod_2466_);
lean_ctor_set_uint8(v_entry_2482_, sizeof(void*)*1, v_isExporting_2478_);
lean_ctor_set_uint8(v_entry_2482_, sizeof(void*)*1 + 1, v_isMeta_2467_);
v___x_2483_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2484_ = lean_box(1);
v___x_2485_ = lean_box(0);
v___x_2528_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2481_, v___x_2483_, v_env_2480_, v___x_2484_, v___x_2485_);
v___x_2529_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg(v___x_2528_, v_entry_2482_);
if (v___x_2529_ == 0)
{
lean_object* v_cls_2530_; lean_object* v___x_2531_; lean_object* v_a_2532_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2539_; lean_object* v___y_2540_; uint8_t v___x_2552_; 
v_cls_2530_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__8));
v___x_2531_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg(v_cls_2530_, v___y_2473_);
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref(v___x_2531_);
v___x_2552_ = lean_unbox(v_a_2532_);
lean_dec(v_a_2532_);
if (v___x_2552_ == 0)
{
lean_dec(v_hint_2468_);
lean_dec(v_mod_2466_);
v___y_2487_ = v___y_2472_;
v___y_2488_ = v___y_2474_;
goto v___jp_2486_;
}
else
{
lean_object* v___x_2553_; lean_object* v___y_2555_; 
v___x_2553_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__14);
if (v_isExporting_2478_ == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__19));
v___y_2555_ = v___x_2562_;
goto v___jp_2554_;
}
else
{
lean_object* v___x_2563_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__20));
v___y_2555_ = v___x_2563_;
goto v___jp_2554_;
}
v___jp_2554_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2556_ = l_Lean_stringToMessageData(v___y_2555_);
v___x_2557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2553_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__16);
v___x_2559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
if (v_isMeta_2467_ == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__17));
v___y_2539_ = v___x_2559_;
v___y_2540_ = v___x_2560_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2561_; 
v___x_2561_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__18));
v___y_2539_ = v___x_2559_;
v___y_2540_ = v___x_2561_;
goto v___jp_2538_;
}
}
}
v___jp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___y_2534_);
lean_ctor_set(v___x_2536_, 1, v___y_2535_);
v___x_2537_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg(v_cls_2530_, v___x_2536_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref(v___x_2537_);
v___y_2487_ = v___y_2472_;
v___y_2488_ = v___y_2474_;
goto v___jp_2486_;
}
else
{
lean_dec_ref(v_entry_2482_);
return v___x_2537_;
}
}
v___jp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2541_ = l_Lean_stringToMessageData(v___y_2540_);
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___y_2539_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__10);
v___x_2544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = l_Lean_MessageData_ofName(v_mod_2466_);
v___x_2546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = l_Lean_Name_isAnonymous(v_hint_2468_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__12);
v___x_2549_ = l_Lean_MessageData_ofName(v_hint_2468_);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___y_2534_ = v___x_2546_;
v___y_2535_ = v___x_2550_;
goto v___jp_2533_;
}
else
{
lean_object* v___x_2551_; 
lean_dec(v_hint_2468_);
v___x_2551_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3);
v___y_2534_ = v___x_2546_;
v___y_2535_ = v___x_2551_;
goto v___jp_2533_;
}
}
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec_ref(v_entry_2482_);
lean_dec(v_hint_2468_);
lean_dec(v_mod_2466_);
v___x_2564_ = lean_box(0);
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
return v___x_2565_;
}
v___jp_2486_:
{
lean_object* v___x_2489_; lean_object* v_toEnvExtension_2490_; lean_object* v_env_2491_; lean_object* v_nextMacroScope_2492_; lean_object* v_ngen_2493_; lean_object* v_auxDeclNGen_2494_; lean_object* v_traceState_2495_; lean_object* v_messages_2496_; lean_object* v_infoState_2497_; lean_object* v_snapshotTasks_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2526_; 
v___x_2489_ = lean_st_ref_take(v___y_2488_);
v_toEnvExtension_2490_ = lean_ctor_get(v___x_2483_, 0);
lean_inc_ref(v_toEnvExtension_2490_);
v_env_2491_ = lean_ctor_get(v___x_2489_, 0);
v_nextMacroScope_2492_ = lean_ctor_get(v___x_2489_, 1);
v_ngen_2493_ = lean_ctor_get(v___x_2489_, 2);
v_auxDeclNGen_2494_ = lean_ctor_get(v___x_2489_, 3);
v_traceState_2495_ = lean_ctor_get(v___x_2489_, 4);
v_messages_2496_ = lean_ctor_get(v___x_2489_, 6);
v_infoState_2497_ = lean_ctor_get(v___x_2489_, 7);
v_snapshotTasks_2498_ = lean_ctor_get(v___x_2489_, 8);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v___x_2489_, 5);
lean_dec(v_unused_2527_);
v___x_2500_ = v___x_2489_;
v_isShared_2501_ = v_isSharedCheck_2526_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_snapshotTasks_2498_);
lean_inc(v_infoState_2497_);
lean_inc(v_messages_2496_);
lean_inc(v_traceState_2495_);
lean_inc(v_auxDeclNGen_2494_);
lean_inc(v_ngen_2493_);
lean_inc(v_nextMacroScope_2492_);
lean_inc(v_env_2491_);
lean_dec(v___x_2489_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2526_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_asyncMode_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
v_asyncMode_2502_ = lean_ctor_get(v_toEnvExtension_2490_, 2);
lean_inc(v_asyncMode_2502_);
lean_dec_ref(v_toEnvExtension_2490_);
v___x_2503_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2483_, v_env_2491_, v_entry_2482_, v_asyncMode_2502_, v___x_2485_);
lean_dec(v_asyncMode_2502_);
v___x_2504_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__5);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 5, v___x_2504_);
lean_ctor_set(v___x_2500_, 0, v___x_2503_);
v___x_2506_ = v___x_2500_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_nextMacroScope_2492_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_ngen_2493_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v_auxDeclNGen_2494_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v_traceState_2495_);
lean_ctor_set(v_reuseFailAlloc_2525_, 5, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2525_, 6, v_messages_2496_);
lean_ctor_set(v_reuseFailAlloc_2525_, 7, v_infoState_2497_);
lean_ctor_set(v_reuseFailAlloc_2525_, 8, v_snapshotTasks_2498_);
v___x_2506_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v_mctx_2509_; lean_object* v_zetaDeltaFVarIds_2510_; lean_object* v_postponed_2511_; lean_object* v_diag_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2523_; 
v___x_2507_ = lean_st_ref_set(v___y_2488_, v___x_2506_);
v___x_2508_ = lean_st_ref_take(v___y_2487_);
v_mctx_2509_ = lean_ctor_get(v___x_2508_, 0);
v_zetaDeltaFVarIds_2510_ = lean_ctor_get(v___x_2508_, 2);
v_postponed_2511_ = lean_ctor_get(v___x_2508_, 3);
v_diag_2512_ = lean_ctor_get(v___x_2508_, 4);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v___x_2508_, 1);
lean_dec(v_unused_2524_);
v___x_2514_ = v___x_2508_;
v_isShared_2515_ = v_isSharedCheck_2523_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_diag_2512_);
lean_inc(v_postponed_2511_);
lean_inc(v_zetaDeltaFVarIds_2510_);
lean_inc(v_mctx_2509_);
lean_dec(v___x_2508_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2523_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__6);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 1, v___x_2516_);
v___x_2518_ = v___x_2514_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_mctx_2509_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_zetaDeltaFVarIds_2510_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_postponed_2511_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_diag_2512_);
v___x_2518_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = lean_st_ref_set(v___y_2487_, v___x_2518_);
v___x_2520_ = lean_box(0);
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___boxed(lean_object* v_mod_2566_, lean_object* v_isMeta_2567_, lean_object* v_hint_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
uint8_t v_isMeta_boxed_2576_; lean_object* v_res_2577_; 
v_isMeta_boxed_2576_ = lean_unbox(v_isMeta_2567_);
v_res_2577_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0(v_mod_2566_, v_isMeta_boxed_2576_, v_hint_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1(lean_object* v___x_2578_, lean_object* v_declName_2579_, lean_object* v_as_2580_, size_t v_sz_2581_, size_t v_i_2582_, lean_object* v_b_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
uint8_t v___x_2591_; 
v___x_2591_ = lean_usize_dec_lt(v_i_2582_, v_sz_2581_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; 
lean_dec(v_declName_2579_);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v_b_2583_);
return v___x_2592_;
}
else
{
lean_object* v___x_2593_; lean_object* v_modules_2594_; lean_object* v___x_2595_; lean_object* v_a_2596_; lean_object* v___x_2597_; lean_object* v_toImport_2598_; lean_object* v_module_2599_; uint8_t v___x_2600_; lean_object* v___x_2601_; 
v___x_2593_ = l_Lean_Environment_header(v___x_2578_);
v_modules_2594_ = lean_ctor_get(v___x_2593_, 3);
lean_inc_ref(v_modules_2594_);
lean_dec_ref(v___x_2593_);
v___x_2595_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2596_ = lean_array_uget_borrowed(v_as_2580_, v_i_2582_);
v___x_2597_ = lean_array_get(v___x_2595_, v_modules_2594_, v_a_2596_);
lean_dec_ref(v_modules_2594_);
v_toImport_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc_ref(v_toImport_2598_);
lean_dec(v___x_2597_);
v_module_2599_ = lean_ctor_get(v_toImport_2598_, 0);
lean_inc(v_module_2599_);
lean_dec_ref(v_toImport_2598_);
v___x_2600_ = 0;
lean_inc(v_declName_2579_);
v___x_2601_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0(v_module_2599_, v___x_2600_, v_declName_2579_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v___x_2602_; size_t v___x_2603_; size_t v___x_2604_; 
lean_dec_ref(v___x_2601_);
v___x_2602_ = lean_box(0);
v___x_2603_ = ((size_t)1ULL);
v___x_2604_ = lean_usize_add(v_i_2582_, v___x_2603_);
v_i_2582_ = v___x_2604_;
v_b_2583_ = v___x_2602_;
goto _start;
}
else
{
lean_dec(v_declName_2579_);
return v___x_2601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1___boxed(lean_object* v___x_2606_, lean_object* v_declName_2607_, lean_object* v_as_2608_, lean_object* v_sz_2609_, lean_object* v_i_2610_, lean_object* v_b_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
size_t v_sz_boxed_2619_; size_t v_i_boxed_2620_; lean_object* v_res_2621_; 
v_sz_boxed_2619_ = lean_unbox_usize(v_sz_2609_);
lean_dec(v_sz_2609_);
v_i_boxed_2620_ = lean_unbox_usize(v_i_2610_);
lean_dec(v_i_2610_);
v_res_2621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1(v___x_2606_, v_declName_2607_, v_as_2608_, v_sz_boxed_2619_, v_i_boxed_2620_, v_b_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec_ref(v_as_2608_);
lean_dec_ref(v___x_2606_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6___redArg(lean_object* v_a_2622_, lean_object* v_x_2623_){
_start:
{
if (lean_obj_tag(v_x_2623_) == 0)
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_box(0);
return v___x_2624_;
}
else
{
lean_object* v_key_2625_; lean_object* v_value_2626_; lean_object* v_tail_2627_; uint8_t v___x_2628_; 
v_key_2625_ = lean_ctor_get(v_x_2623_, 0);
v_value_2626_ = lean_ctor_get(v_x_2623_, 1);
v_tail_2627_ = lean_ctor_get(v_x_2623_, 2);
v___x_2628_ = lean_name_eq(v_key_2625_, v_a_2622_);
if (v___x_2628_ == 0)
{
v_x_2623_ = v_tail_2627_;
goto _start;
}
else
{
lean_object* v___x_2630_; 
lean_inc(v_value_2626_);
v___x_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2630_, 0, v_value_2626_);
return v___x_2630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_2631_, lean_object* v_x_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6___redArg(v_a_2631_, v_x_2632_);
lean_dec(v_x_2632_);
lean_dec(v_a_2631_);
return v_res_2633_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2634_; uint64_t v___x_2635_; 
v___x_2634_ = lean_unsigned_to_nat(1723u);
v___x_2635_ = lean_uint64_of_nat(v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg(lean_object* v_m_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_buckets_2638_; lean_object* v___x_2639_; uint64_t v___y_2641_; 
v_buckets_2638_ = lean_ctor_get(v_m_2636_, 1);
v___x_2639_ = lean_array_get_size(v_buckets_2638_);
if (lean_obj_tag(v_a_2637_) == 0)
{
uint64_t v___x_2655_; 
v___x_2655_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___closed__0);
v___y_2641_ = v___x_2655_;
goto v___jp_2640_;
}
else
{
uint64_t v_hash_2656_; 
v_hash_2656_ = lean_ctor_get_uint64(v_a_2637_, sizeof(void*)*2);
v___y_2641_ = v_hash_2656_;
goto v___jp_2640_;
}
v___jp_2640_:
{
uint64_t v___x_2642_; uint64_t v___x_2643_; uint64_t v_fold_2644_; uint64_t v___x_2645_; uint64_t v___x_2646_; uint64_t v___x_2647_; size_t v___x_2648_; size_t v___x_2649_; size_t v___x_2650_; size_t v___x_2651_; size_t v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2642_ = 32ULL;
v___x_2643_ = lean_uint64_shift_right(v___y_2641_, v___x_2642_);
v_fold_2644_ = lean_uint64_xor(v___y_2641_, v___x_2643_);
v___x_2645_ = 16ULL;
v___x_2646_ = lean_uint64_shift_right(v_fold_2644_, v___x_2645_);
v___x_2647_ = lean_uint64_xor(v_fold_2644_, v___x_2646_);
v___x_2648_ = lean_uint64_to_usize(v___x_2647_);
v___x_2649_ = lean_usize_of_nat(v___x_2639_);
v___x_2650_ = ((size_t)1ULL);
v___x_2651_ = lean_usize_sub(v___x_2649_, v___x_2650_);
v___x_2652_ = lean_usize_land(v___x_2648_, v___x_2651_);
v___x_2653_ = lean_array_uget_borrowed(v_buckets_2638_, v___x_2652_);
v___x_2654_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6___redArg(v_a_2637_, v___x_2653_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg(v_m_2657_, v_a_2658_);
lean_dec(v_a_2658_);
lean_dec_ref(v_m_2657_);
return v_res_2659_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2662_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__1));
v___x_2663_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__0));
v___x_2664_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2663_, v___x_2662_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0(lean_object* v_declName_2667_, uint8_t v_isMeta_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; lean_object* v_env_2680_; lean_object* v___y_2682_; lean_object* v___x_2695_; 
v___x_2676_ = lean_st_ref_get(v___y_2674_);
v_env_2680_ = lean_ctor_get(v___x_2676_, 0);
lean_inc_ref(v_env_2680_);
lean_dec(v___x_2676_);
v___x_2695_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2680_, v_declName_2667_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_dec_ref(v_env_2680_);
lean_dec(v_declName_2667_);
goto v___jp_2677_;
}
else
{
lean_object* v_val_2696_; lean_object* v___x_2697_; lean_object* v_modules_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v_val_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_val_2696_);
lean_dec_ref(v___x_2695_);
v___x_2697_ = l_Lean_Environment_header(v_env_2680_);
v_modules_2698_ = lean_ctor_get(v___x_2697_, 3);
lean_inc_ref(v_modules_2698_);
lean_dec_ref(v___x_2697_);
v___x_2699_ = lean_array_get_size(v_modules_2698_);
v___x_2700_ = lean_nat_dec_lt(v_val_2696_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_dec_ref(v_modules_2698_);
lean_dec(v_val_2696_);
lean_dec_ref(v_env_2680_);
lean_dec(v_declName_2667_);
goto v___jp_2677_;
}
else
{
lean_object* v___x_2701_; lean_object* v_env_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___y_2706_; 
v___x_2701_ = lean_st_ref_get(v___y_2674_);
v_env_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc_ref(v_env_2702_);
lean_dec(v___x_2701_);
v___x_2703_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__2);
v___x_2704_ = lean_array_fget(v_modules_2698_, v_val_2696_);
lean_dec(v_val_2696_);
lean_dec_ref(v_modules_2698_);
if (v_isMeta_2668_ == 0)
{
lean_dec_ref(v_env_2702_);
v___y_2706_ = v_isMeta_2668_;
goto v___jp_2705_;
}
else
{
uint8_t v___x_2717_; 
lean_inc(v_declName_2667_);
v___x_2717_ = l_Lean_isMarkedMeta(v_env_2702_, v_declName_2667_);
if (v___x_2717_ == 0)
{
v___y_2706_ = v_isMeta_2668_;
goto v___jp_2705_;
}
else
{
uint8_t v___x_2718_; 
v___x_2718_ = 0;
v___y_2706_ = v___x_2718_;
goto v___jp_2705_;
}
}
v___jp_2705_:
{
lean_object* v_toImport_2707_; lean_object* v_module_2708_; lean_object* v___x_2709_; 
v_toImport_2707_ = lean_ctor_get(v___x_2704_, 0);
lean_inc_ref(v_toImport_2707_);
lean_dec(v___x_2704_);
v_module_2708_ = lean_ctor_get(v_toImport_2707_, 0);
lean_inc(v_module_2708_);
lean_dec_ref(v_toImport_2707_);
lean_inc(v_declName_2667_);
v___x_2709_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0(v_module_2708_, v___y_2706_, v_declName_2667_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec_ref(v___x_2709_);
v___x_2710_ = l_Lean_indirectModUseExt;
v___x_2711_ = lean_box(1);
v___x_2712_ = lean_box(0);
lean_inc_ref(v_env_2680_);
v___x_2713_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2703_, v___x_2710_, v_env_2680_, v___x_2711_, v___x_2712_);
v___x_2714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg(v___x_2713_, v_declName_2667_);
lean_dec(v___x_2713_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v___x_2715_; 
v___x_2715_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__3));
v___y_2682_ = v___x_2715_;
goto v___jp_2681_;
}
else
{
lean_object* v_val_2716_; 
v_val_2716_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_val_2716_);
lean_dec_ref(v___x_2714_);
v___y_2682_ = v_val_2716_;
goto v___jp_2681_;
}
}
else
{
lean_dec_ref(v_env_2680_);
lean_dec(v_declName_2667_);
return v___x_2709_;
}
}
}
}
v___jp_2677_:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = lean_box(0);
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
return v___x_2679_;
}
v___jp_2681_:
{
lean_object* v___x_2683_; size_t v_sz_2684_; size_t v___x_2685_; lean_object* v___x_2686_; 
v___x_2683_ = lean_box(0);
v_sz_2684_ = lean_array_size(v___y_2682_);
v___x_2685_ = ((size_t)0ULL);
v___x_2686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1(v_env_2680_, v_declName_2667_, v___y_2682_, v_sz_2684_, v___x_2685_, v___x_2683_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
lean_dec_ref(v___y_2682_);
lean_dec_ref(v_env_2680_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v___x_2686_, 0);
lean_dec(v_unused_2694_);
v___x_2688_ = v___x_2686_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v___x_2686_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2683_);
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2683_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
return v___x_2686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___boxed(lean_object* v_declName_2719_, lean_object* v_isMeta_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
uint8_t v_isMeta_boxed_2728_; lean_object* v_res_2729_; 
v_isMeta_boxed_2728_ = lean_unbox(v_isMeta_2720_);
v_res_2729_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0(v_declName_2719_, v_isMeta_boxed_2728_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
return v_res_2729_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = lean_box(1);
v___x_2731_ = l_Lean_MessageData_ofFormat(v___x_2730_);
return v___x_2731_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__3(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__2));
v___x_2736_ = l_Lean_MessageData_ofFormat(v___x_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10(lean_object* v_x_2737_, lean_object* v_x_2738_){
_start:
{
if (lean_obj_tag(v_x_2738_) == 0)
{
return v_x_2737_;
}
else
{
lean_object* v_head_2739_; lean_object* v_tail_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2762_; 
v_head_2739_ = lean_ctor_get(v_x_2738_, 0);
v_tail_2740_ = lean_ctor_get(v_x_2738_, 1);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_x_2738_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2742_ = v_x_2738_;
v_isShared_2743_ = v_isSharedCheck_2762_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_tail_2740_);
lean_inc(v_head_2739_);
lean_dec(v_x_2738_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2762_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v_before_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2760_; 
v_before_2744_ = lean_ctor_get(v_head_2739_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_head_2739_);
if (v_isSharedCheck_2760_ == 0)
{
lean_object* v_unused_2761_; 
v_unused_2761_ = lean_ctor_get(v_head_2739_, 1);
lean_dec(v_unused_2761_);
v___x_2746_ = v_head_2739_;
v_isShared_2747_ = v_isSharedCheck_2760_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_before_2744_);
lean_dec(v_head_2739_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2760_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2748_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__0);
if (v_isShared_2747_ == 0)
{
lean_ctor_set_tag(v___x_2746_, 7);
lean_ctor_set(v___x_2746_, 1, v___x_2748_);
lean_ctor_set(v___x_2746_, 0, v_x_2737_);
v___x_2750_ = v___x_2746_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_x_2737_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2751_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__3);
if (v_isShared_2743_ == 0)
{
lean_ctor_set_tag(v___x_2742_, 7);
lean_ctor_set(v___x_2742_, 1, v___x_2751_);
lean_ctor_set(v___x_2742_, 0, v___x_2750_);
v___x_2753_ = v___x_2742_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = l_Lean_MessageData_ofSyntax(v_before_2744_);
v___x_2755_ = l_Lean_indentD(v___x_2754_);
v___x_2756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2753_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v_x_2737_ = v___x_2756_;
v_x_2738_ = v_tail_2740_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9(lean_object* v_opts_2763_, lean_object* v_opt_2764_){
_start:
{
lean_object* v_name_2765_; lean_object* v_defValue_2766_; lean_object* v_map_2767_; lean_object* v___x_2768_; 
v_name_2765_ = lean_ctor_get(v_opt_2764_, 0);
v_defValue_2766_ = lean_ctor_get(v_opt_2764_, 1);
v_map_2767_ = lean_ctor_get(v_opts_2763_, 0);
v___x_2768_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2767_, v_name_2765_);
if (lean_obj_tag(v___x_2768_) == 0)
{
uint8_t v___x_2769_; 
v___x_2769_ = lean_unbox(v_defValue_2766_);
return v___x_2769_;
}
else
{
lean_object* v_val_2770_; 
v_val_2770_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_val_2770_);
lean_dec_ref(v___x_2768_);
if (lean_obj_tag(v_val_2770_) == 1)
{
uint8_t v_v_2771_; 
v_v_2771_ = lean_ctor_get_uint8(v_val_2770_, 0);
lean_dec_ref(v_val_2770_);
return v_v_2771_;
}
else
{
uint8_t v___x_2772_; 
lean_dec(v_val_2770_);
v___x_2772_ = lean_unbox(v_defValue_2766_);
return v___x_2772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___boxed(lean_object* v_opts_2773_, lean_object* v_opt_2774_){
_start:
{
uint8_t v_res_2775_; lean_object* v_r_2776_; 
v_res_2775_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9(v_opts_2773_, v_opt_2774_);
lean_dec_ref(v_opt_2774_);
lean_dec_ref(v_opts_2773_);
v_r_2776_ = lean_box(v_res_2775_);
return v_r_2776_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__1));
v___x_2781_ = l_Lean_MessageData_ofFormat(v___x_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg(lean_object* v_msgData_2782_, lean_object* v_macroStack_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_options_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v_options_2786_ = lean_ctor_get(v___y_2784_, 2);
v___x_2787_ = l_Lean_Elab_pp_macroStack;
v___x_2788_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9(v_options_2786_, v___x_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; 
lean_dec(v_macroStack_2783_);
v___x_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2789_, 0, v_msgData_2782_);
return v___x_2789_;
}
else
{
if (lean_obj_tag(v_macroStack_2783_) == 0)
{
lean_object* v___x_2790_; 
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v_msgData_2782_);
return v___x_2790_;
}
else
{
lean_object* v_head_2791_; lean_object* v_after_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2807_; 
v_head_2791_ = lean_ctor_get(v_macroStack_2783_, 0);
lean_inc(v_head_2791_);
v_after_2792_ = lean_ctor_get(v_head_2791_, 1);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_head_2791_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v_head_2791_, 0);
lean_dec(v_unused_2808_);
v___x_2794_ = v_head_2791_;
v_isShared_2795_ = v_isSharedCheck_2807_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_after_2792_);
lean_dec(v_head_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2807_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2796_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10___closed__0);
if (v_isShared_2795_ == 0)
{
lean_ctor_set_tag(v___x_2794_, 7);
lean_ctor_set(v___x_2794_, 1, v___x_2796_);
lean_ctor_set(v___x_2794_, 0, v_msgData_2782_);
v___x_2798_ = v___x_2794_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_msgData_2782_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v___x_2796_);
v___x_2798_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v_msgData_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2799_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__2);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = l_Lean_MessageData_ofSyntax(v_after_2792_);
v___x_2802_ = l_Lean_indentD(v___x_2801_);
v_msgData_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2803_, 0, v___x_2800_);
lean_ctor_set(v_msgData_2803_, 1, v___x_2802_);
v___x_2804_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__10(v_msgData_2803_, v_macroStack_2783_);
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_2809_, lean_object* v_macroStack_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg(v_msgData_2809_, v_macroStack_2810_, v___y_2811_);
lean_dec_ref(v___y_2811_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(lean_object* v_msg_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_ref_2822_; lean_object* v___x_2823_; lean_object* v_a_2824_; lean_object* v_macroStack_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2836_; 
v_ref_2822_ = lean_ctor_get(v___y_2819_, 5);
v___x_2823_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3_spec__8(v_msg_2814_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref(v___x_2823_);
v_macroStack_2825_ = lean_ctor_get(v___y_2815_, 1);
lean_inc(v_macroStack_2825_);
lean_dec_ref(v___y_2815_);
lean_inc(v_macroStack_2825_);
v___x_2826_ = l_Lean_Elab_getBetterRef(v_ref_2822_, v_macroStack_2825_);
v___x_2827_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg(v_a_2824_, v_macroStack_2825_, v___y_2819_);
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2836_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2836_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2826_);
lean_ctor_set(v___x_2832_, 1, v_a_2828_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set_tag(v___x_2830_, 1);
lean_ctor_set(v___x_2830_, 0, v___x_2832_);
v___x_2834_ = v___x_2830_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg___boxed(lean_object* v_msg_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(v_msg_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
return v_res_2845_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0));
v___x_2848_ = l_Lean_stringToMessageData(v___x_2847_);
return v___x_2848_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__2));
v___x_2851_ = l_Lean_stringToMessageData(v___x_2850_);
return v___x_2851_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__4));
v___x_2854_ = l_Lean_stringToMessageData(v___x_2853_);
return v___x_2854_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__7));
v___x_2862_ = l_Lean_stringToMessageData(v___x_2861_);
return v___x_2862_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_));
v___x_2864_ = l_Lean_MessageData_ofName(v___x_2863_);
return v___x_2864_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__10(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__9, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__9);
v___x_2866_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__8, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__8);
v___x_2867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
lean_ctor_set(v___x_2867_, 1, v___x_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object* v_optConfig_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; uint8_t v___y_2887_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; uint8_t v_recover_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; uint8_t v___x_2914_; uint8_t v___x_2915_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; 
v_recover_2909_ = lean_ctor_get_uint8(v_a_2869_, sizeof(void*)*1);
lean_inc(v_optConfig_2868_);
v___x_2910_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_2868_);
v___x_2911_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_2910_);
v___x_2912_ = lean_array_get_size(v___x_2911_);
v___x_2913_ = lean_unsigned_to_nat(0u);
v___x_2914_ = lean_nat_dec_eq(v___x_2912_, v___x_2913_);
v___x_2915_ = 1;
if (v___x_2914_ == 0)
{
lean_object* v___x_2963_; lean_object* v_fileName_2964_; lean_object* v_fileMap_2965_; lean_object* v_options_2966_; lean_object* v_currRecDepth_2967_; lean_object* v_maxRecDepth_2968_; lean_object* v_ref_2969_; lean_object* v_currNamespace_2970_; lean_object* v_openDecls_2971_; lean_object* v_initHeartbeats_2972_; lean_object* v_maxHeartbeats_2973_; lean_object* v_quotContext_2974_; lean_object* v_currMacroScope_2975_; uint8_t v_diag_2976_; lean_object* v_cancelTk_x3f_2977_; uint8_t v_suppressElabErrors_2978_; lean_object* v_inheritedTraceOptions_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3000_; 
v___x_2963_ = lean_st_ref_get(v_a_2875_);
v_fileName_2964_ = lean_ctor_get(v_a_2874_, 0);
v_fileMap_2965_ = lean_ctor_get(v_a_2874_, 1);
v_options_2966_ = lean_ctor_get(v_a_2874_, 2);
v_currRecDepth_2967_ = lean_ctor_get(v_a_2874_, 3);
v_maxRecDepth_2968_ = lean_ctor_get(v_a_2874_, 4);
v_ref_2969_ = lean_ctor_get(v_a_2874_, 5);
v_currNamespace_2970_ = lean_ctor_get(v_a_2874_, 6);
v_openDecls_2971_ = lean_ctor_get(v_a_2874_, 7);
v_initHeartbeats_2972_ = lean_ctor_get(v_a_2874_, 8);
v_maxHeartbeats_2973_ = lean_ctor_get(v_a_2874_, 9);
v_quotContext_2974_ = lean_ctor_get(v_a_2874_, 10);
v_currMacroScope_2975_ = lean_ctor_get(v_a_2874_, 11);
v_diag_2976_ = lean_ctor_get_uint8(v_a_2874_, sizeof(void*)*14);
v_cancelTk_x3f_2977_ = lean_ctor_get(v_a_2874_, 12);
v_suppressElabErrors_2978_ = lean_ctor_get_uint8(v_a_2874_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2979_ = lean_ctor_get(v_a_2874_, 13);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_a_2874_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2981_ = v_a_2874_;
v_isShared_2982_ = v_isSharedCheck_3000_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_inheritedTraceOptions_2979_);
lean_inc(v_cancelTk_x3f_2977_);
lean_inc(v_currMacroScope_2975_);
lean_inc(v_quotContext_2974_);
lean_inc(v_maxHeartbeats_2973_);
lean_inc(v_initHeartbeats_2972_);
lean_inc(v_openDecls_2971_);
lean_inc(v_currNamespace_2970_);
lean_inc(v_ref_2969_);
lean_inc(v_maxRecDepth_2968_);
lean_inc(v_currRecDepth_2967_);
lean_inc(v_options_2966_);
lean_inc(v_fileMap_2965_);
lean_inc(v_fileName_2964_);
lean_dec(v_a_2874_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3000_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v_env_2983_; lean_object* v_ref_2984_; lean_object* v___x_2986_; 
v_env_2983_ = lean_ctor_get(v___x_2963_, 0);
lean_inc_ref(v_env_2983_);
lean_dec(v___x_2963_);
v_ref_2984_ = l_Lean_replaceRef(v_optConfig_2868_, v_ref_2969_);
lean_dec(v_ref_2969_);
lean_dec(v_optConfig_2868_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 5, v_ref_2984_);
v___x_2986_ = v___x_2981_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_fileName_2964_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_fileMap_2965_);
lean_ctor_set(v_reuseFailAlloc_2999_, 2, v_options_2966_);
lean_ctor_set(v_reuseFailAlloc_2999_, 3, v_currRecDepth_2967_);
lean_ctor_set(v_reuseFailAlloc_2999_, 4, v_maxRecDepth_2968_);
lean_ctor_set(v_reuseFailAlloc_2999_, 5, v_ref_2984_);
lean_ctor_set(v_reuseFailAlloc_2999_, 6, v_currNamespace_2970_);
lean_ctor_set(v_reuseFailAlloc_2999_, 7, v_openDecls_2971_);
lean_ctor_set(v_reuseFailAlloc_2999_, 8, v_initHeartbeats_2972_);
lean_ctor_set(v_reuseFailAlloc_2999_, 9, v_maxHeartbeats_2973_);
lean_ctor_set(v_reuseFailAlloc_2999_, 10, v_quotContext_2974_);
lean_ctor_set(v_reuseFailAlloc_2999_, 11, v_currMacroScope_2975_);
lean_ctor_set(v_reuseFailAlloc_2999_, 12, v_cancelTk_x3f_2977_);
lean_ctor_set(v_reuseFailAlloc_2999_, 13, v_inheritedTraceOptions_2979_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*14, v_diag_2976_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*14 + 1, v_suppressElabErrors_2978_);
v___x_2986_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2987_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_));
v___x_2988_ = l_Lean_Environment_contains(v_env_2983_, v___x_2987_, v___x_2915_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v___x_2911_);
v___x_2989_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__10, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__10_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__10);
v___x_2990_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(v___x_2989_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v___x_2986_, v_a_2875_);
lean_dec(v_a_2875_);
lean_dec_ref(v___x_2986_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
else
{
v___y_2917_ = v_a_2870_;
v___y_2918_ = v_a_2871_;
v___y_2919_ = v_a_2872_;
v___y_2920_ = v_a_2873_;
v___y_2921_ = v___x_2986_;
v___y_2922_ = v_a_2875_;
goto v___jp_2916_;
}
}
}
}
else
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
lean_dec_ref(v___x_2911_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_optConfig_2868_);
v___x_3001_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__6));
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
return v___x_3002_;
}
v___jp_2877_:
{
if (v___y_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
lean_dec_ref(v___y_2885_);
v___x_2888_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__1, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__1);
v___x_2889_ = l_Lean_MessageData_ofExpr(v___y_2884_);
v___x_2890_ = l_Lean_indentD(v___x_2889_);
v___x_2891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2888_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__3, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__3);
v___x_2893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
v___x_2894_ = l_Lean_Exception_toMessageData(v___y_2882_);
v___x_2895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2893_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(v___x_2895_, v___y_2879_, v___y_2883_, v___y_2878_, v___y_2880_, v___y_2881_, v___y_2886_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2883_);
return v___x_2896_;
}
else
{
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v___y_2878_);
return v___y_2885_;
}
}
v___jp_2897_:
{
lean_object* v___x_2905_; 
lean_inc(v___y_2904_);
lean_inc_ref(v___y_2903_);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc_ref(v___y_2898_);
v___x_2905_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(v___y_2898_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec_ref(v___y_2898_);
return v___x_2905_;
}
else
{
lean_object* v_a_2906_; uint8_t v___x_2907_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
v___x_2907_ = l_Lean_Exception_isInterrupt(v_a_2906_);
if (v___x_2907_ == 0)
{
uint8_t v___x_2908_; 
lean_inc(v_a_2906_);
v___x_2908_ = l_Lean_Exception_isRuntime(v_a_2906_);
v___y_2878_ = v___y_2901_;
v___y_2879_ = v___y_2899_;
v___y_2880_ = v___y_2902_;
v___y_2881_ = v___y_2903_;
v___y_2882_ = v_a_2906_;
v___y_2883_ = v___y_2900_;
v___y_2884_ = v___y_2898_;
v___y_2885_ = v___x_2905_;
v___y_2886_ = v___y_2904_;
v___y_2887_ = v___x_2908_;
goto v___jp_2877_;
}
else
{
v___y_2878_ = v___y_2901_;
v___y_2879_ = v___y_2899_;
v___y_2880_ = v___y_2902_;
v___y_2881_ = v___y_2903_;
v___y_2882_ = v_a_2906_;
v___y_2883_ = v___y_2900_;
v___y_2884_ = v___y_2898_;
v___y_2885_ = v___x_2905_;
v___y_2886_ = v___y_2904_;
v___y_2887_ = v___x_2907_;
goto v___jp_2877_;
}
}
}
v___jp_2916_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_));
v___x_2924_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0(v___x_2923_, v___x_2915_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v___x_2925_; 
lean_dec_ref(v___x_2924_);
lean_inc(v___y_2922_);
lean_inc_ref(v___y_2921_);
lean_inc(v___y_2920_);
lean_inc_ref(v___y_2919_);
lean_inc(v___y_2918_);
lean_inc_ref(v___y_2917_);
v___x_2925_ = l_Lean_Elab_Tactic_elabConfig(v_recover_2909_, v___x_2923_, v___x_2911_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2946_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2928_ = v___x_2925_;
v_isShared_2929_ = v_isSharedCheck_2946_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2925_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2946_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
uint8_t v___x_2930_; 
v___x_2930_ = l_Lean_Expr_hasSyntheticSorry(v_a_2926_);
if (v___x_2930_ == 0)
{
uint8_t v___x_2931_; 
lean_del_object(v___x_2928_);
v___x_2931_ = l_Lean_Expr_hasSorry(v_a_2926_);
if (v___x_2931_ == 0)
{
v___y_2898_ = v_a_2926_;
v___y_2899_ = v___y_2917_;
v___y_2900_ = v___y_2918_;
v___y_2901_ = v___y_2919_;
v___y_2902_ = v___y_2920_;
v___y_2903_ = v___y_2921_;
v___y_2904_ = v___y_2922_;
goto v___jp_2897_;
}
else
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v_a_2926_);
v___x_2932_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__5, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__5);
v___x_2933_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(v___x_2932_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2944_; 
lean_dec(v_a_2926_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
v___x_2942_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__6));
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 0, v___x_2942_);
v___x_2944_ = v___x_2928_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
v_a_2947_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2925_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2925_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v___x_2911_);
v_a_2955_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2924_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2924_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object* v_optConfig_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_optConfig_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
lean_dec_ref(v_a_3004_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object* v_optConfig_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_optConfig_3013_, v_a_3014_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object* v_optConfig_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Lean_Elab_Tactic_elabRewriteConfig(v_optConfig_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1(lean_object* v_00_u03b1_3035_, lean_object* v_msg_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(v_msg_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___boxed(lean_object* v_00_u03b1_3045_, lean_object* v_msg_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1(v_00_u03b1_3045_, v_msg_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2(lean_object* v_cls_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg(v_cls_3055_, v___y_3060_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2(v_cls_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2(lean_object* v_00_u03b2_3073_, lean_object* v_m_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg(v_m_3074_, v_a_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3077_, lean_object* v_m_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2(v_00_u03b2_3077_, v_m_3078_, v_a_3079_);
lean_dec(v_a_3079_);
lean_dec_ref(v_m_3078_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4(lean_object* v_msgData_3081_, lean_object* v_macroStack_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg(v_msgData_3081_, v_macroStack_3082_, v___y_3087_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___boxed(lean_object* v_msgData_3091_, lean_object* v_macroStack_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4(v_msgData_3091_, v_macroStack_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
return v_res_3100_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3101_, lean_object* v_x_3102_, lean_object* v_x_3103_){
_start:
{
uint8_t v___x_3104_; 
v___x_3104_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg(v_x_3102_, v_x_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3105_, lean_object* v_x_3106_, lean_object* v_x_3107_){
_start:
{
uint8_t v_res_3108_; lean_object* v_r_3109_; 
v_res_3108_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1(v_00_u03b2_3105_, v_x_3106_, v_x_3107_);
lean_dec_ref(v_x_3107_);
v_r_3109_ = lean_box(v_res_3108_);
return v_r_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3(lean_object* v_cls_3110_, lean_object* v_msg_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___redArg(v_cls_3110_, v_msg_3111_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3___boxed(lean_object* v_cls_3120_, lean_object* v_msg_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__3(v_cls_3120_, v_msg_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_3130_, lean_object* v_a_3131_, lean_object* v_x_3132_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6___redArg(v_a_3131_, v_x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_3134_, lean_object* v_a_3135_, lean_object* v_x_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__6(v_00_u03b2_3134_, v_a_3135_, v_x_3136_);
lean_dec(v_x_3136_);
lean_dec(v_a_3135_);
return v_res_3137_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3138_, lean_object* v_x_3139_, size_t v_x_3140_, lean_object* v_x_3141_){
_start:
{
uint8_t v___x_3142_; 
v___x_3142_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3139_, v_x_3140_, v_x_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3143_, lean_object* v_x_3144_, lean_object* v_x_3145_, lean_object* v_x_3146_){
_start:
{
size_t v_x_13071__boxed_3147_; uint8_t v_res_3148_; lean_object* v_r_3149_; 
v_x_13071__boxed_3147_ = lean_unbox_usize(v_x_3145_);
lean_dec(v_x_3145_);
v_res_3148_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3143_, v_x_3144_, v_x_13071__boxed_3147_, v_x_3146_);
lean_dec_ref(v_x_3146_);
v_r_3149_ = lean_box(v_res_3148_);
return v_r_3149_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_3150_, lean_object* v_keys_3151_, lean_object* v_vals_3152_, lean_object* v_heq_3153_, lean_object* v_i_3154_, lean_object* v_k_3155_){
_start:
{
uint8_t v___x_3156_; 
v___x_3156_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_3151_, v_i_3154_, v_k_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_3157_, lean_object* v_keys_3158_, lean_object* v_vals_3159_, lean_object* v_heq_3160_, lean_object* v_i_3161_, lean_object* v_k_3162_){
_start:
{
uint8_t v_res_3163_; lean_object* v_r_3164_; 
v_res_3163_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_3157_, v_keys_3158_, v_vals_3159_, v_heq_3160_, v_i_3161_, v_k_3162_);
lean_dec_ref(v_k_3162_);
lean_dec_ref(v_vals_3159_);
lean_dec_ref(v_keys_3158_);
v_r_3164_ = lean_box(v_res_3163_);
return v_r_3164_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3));
v___x_3172_ = l_Lean_MessageData_ofFormat(v___x_3171_);
return v___x_3172_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4);
v___x_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object* v_x_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3185_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1));
v___x_3186_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5);
v___x_3187_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3185_, v_x_3175_, v___x_3186_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object* v_x_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(v_x_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object* v_term_3199_, uint8_t v_symm_3200_, lean_object* v_a_3201_, lean_object* v_x_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_term_3199_, v_symm_3200_, v_x_3202_, v_a_3201_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object* v_term_3213_, lean_object* v_symm_3214_, lean_object* v_a_3215_, lean_object* v_x_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
uint8_t v_symm_boxed_3226_; lean_object* v_res_3227_; 
v_symm_boxed_3226_ = lean_unbox(v_symm_3214_);
v_res_3227_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(v_term_3213_, v_symm_boxed_3226_, v_a_3215_, v_x_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object* v_a_3228_, lean_object* v___x_3229_, lean_object* v___f_3230_, uint8_t v_symm_3231_, lean_object* v_term_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___x_3242_; lean_object* v___f_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3242_ = lean_box(v_symm_3231_);
lean_inc_ref(v_a_3228_);
lean_inc(v_term_3232_);
v___f_3243_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed), 13, 3);
lean_closure_set(v___f_3243_, 0, v_term_3232_);
lean_closure_set(v___f_3243_, 1, v___x_3242_);
lean_closure_set(v___f_3243_, 2, v_a_3228_);
v___x_3244_ = lean_box(v_symm_3231_);
v___x_3245_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(v___x_3245_, 0, v_term_3232_);
lean_closure_set(v___x_3245_, 1, v___x_3244_);
lean_closure_set(v___x_3245_, 2, v_a_3228_);
v___x_3246_ = l_Lean_Elab_Tactic_withLocation(v___x_3229_, v___f_3243_, v___x_3245_, v___f_3230_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object* v_a_3247_, lean_object* v___x_3248_, lean_object* v___f_3249_, lean_object* v_symm_3250_, lean_object* v_term_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
uint8_t v_symm_boxed_3261_; lean_object* v_res_3262_; 
v_symm_boxed_3261_ = lean_unbox(v_symm_3250_);
v_res_3262_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(v_a_3247_, v___x_3248_, v___f_3249_, v_symm_boxed_3261_, v_term_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___x_3248_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object* v_stx_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3274_ = lean_unsigned_to_nat(1u);
v___x_3275_ = l_Lean_Syntax_getArg(v_stx_3264_, v___x_3274_);
lean_inc(v_a_3272_);
lean_inc_ref(v_a_3271_);
lean_inc(v_a_3270_);
lean_inc_ref(v_a_3269_);
lean_inc(v_a_3268_);
lean_inc_ref(v_a_3267_);
v___x_3276_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v___x_3275_, v_a_3265_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___f_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___f_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v___x_3276_);
v___f_3278_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__0));
v___x_3279_ = lean_unsigned_to_nat(3u);
v___x_3280_ = l_Lean_Syntax_getArg(v_stx_3264_, v___x_3279_);
v___x_3281_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_3280_);
lean_dec(v___x_3280_);
v___f_3282_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed), 14, 3);
lean_closure_set(v___f_3282_, 0, v_a_3277_);
lean_closure_set(v___f_3282_, 1, v___x_3281_);
lean_closure_set(v___f_3282_, 2, v___f_3278_);
v___x_3283_ = lean_unsigned_to_nat(0u);
v___x_3284_ = l_Lean_Syntax_getArg(v_stx_3264_, v___x_3283_);
v___x_3285_ = lean_unsigned_to_nat(2u);
v___x_3286_ = l_Lean_Syntax_getArg(v_stx_3264_, v___x_3285_);
v___x_3287_ = l_Lean_Elab_Tactic_withRWRulesSeq(v___x_3284_, v___x_3286_, v___f_3282_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
lean_dec(v___x_3286_);
return v___x_3287_;
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec(v_a_3272_);
lean_dec_ref(v_a_3271_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
v_a_3288_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3276_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3276_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object* v_stx_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_Elab_Tactic_evalRewriteSeq(v_stx_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_);
lean_dec(v_stx_3296_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3322_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3323_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2));
v___x_3324_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_3325_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___boxed), 10, 0);
v___x_3326_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3322_, v___x_3323_, v___x_3324_, v___x_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(lean_object* v_a_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3(){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3355_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_3356_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6));
v___x_3357_ = l_Lean_addBuiltinDeclarationRanges(v___x_3355_, v___x_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(lean_object* v_a_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
return v_res_3359_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Rewrite(builtin);
}
#ifdef __cplusplus
}
#endif
