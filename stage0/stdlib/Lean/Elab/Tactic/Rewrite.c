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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__13_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__18_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__19;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rewriteSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 231, 198, 107, 115, 169, 96, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalRewriteSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(131, 252, 0, 80, 225, 242, 251, 126)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(lean_object*);
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
lean_object* v_fileName_526_; lean_object* v_fileMap_527_; lean_object* v_options_528_; lean_object* v_currRecDepth_529_; lean_object* v_maxRecDepth_530_; lean_object* v_ref_531_; lean_object* v_currNamespace_532_; lean_object* v_openDecls_533_; lean_object* v_initHeartbeats_534_; lean_object* v_maxHeartbeats_535_; lean_object* v_quotContext_536_; lean_object* v_currMacroScope_537_; uint8_t v_diag_538_; lean_object* v_cancelTk_x3f_539_; uint8_t v_suppressElabErrors_540_; lean_object* v_inheritedTraceOptions_541_; lean_object* v_ref_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
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
v_ref_542_ = l_Lean_replaceRef(v_ref_515_, v_ref_531_);
lean_inc_ref(v_inheritedTraceOptions_541_);
lean_inc(v_cancelTk_x3f_539_);
lean_inc(v_currMacroScope_537_);
lean_inc(v_quotContext_536_);
lean_inc(v_maxHeartbeats_535_);
lean_inc(v_initHeartbeats_534_);
lean_inc(v_openDecls_533_);
lean_inc(v_currNamespace_532_);
lean_inc(v_maxRecDepth_530_);
lean_inc(v_currRecDepth_529_);
lean_inc_ref(v_options_528_);
lean_inc_ref(v_fileMap_527_);
lean_inc_ref(v_fileName_526_);
v___x_543_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_543_, 0, v_fileName_526_);
lean_ctor_set(v___x_543_, 1, v_fileMap_527_);
lean_ctor_set(v___x_543_, 2, v_options_528_);
lean_ctor_set(v___x_543_, 3, v_currRecDepth_529_);
lean_ctor_set(v___x_543_, 4, v_maxRecDepth_530_);
lean_ctor_set(v___x_543_, 5, v_ref_542_);
lean_ctor_set(v___x_543_, 6, v_currNamespace_532_);
lean_ctor_set(v___x_543_, 7, v_openDecls_533_);
lean_ctor_set(v___x_543_, 8, v_initHeartbeats_534_);
lean_ctor_set(v___x_543_, 9, v_maxHeartbeats_535_);
lean_ctor_set(v___x_543_, 10, v_quotContext_536_);
lean_ctor_set(v___x_543_, 11, v_currMacroScope_537_);
lean_ctor_set(v___x_543_, 12, v_cancelTk_x3f_539_);
lean_ctor_set(v___x_543_, 13, v_inheritedTraceOptions_541_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*14, v_diag_538_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*14 + 1, v_suppressElabErrors_540_);
v___x_544_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___redArg(v_msg_516_, v___y_521_, v___y_522_, v___x_543_, v___y_524_);
lean_dec_ref(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___redArg___boxed(lean_object* v_ref_545_, lean_object* v_msg_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___redArg(v_ref_545_, v_msg_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v_ref_545_);
return v_res_556_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__1(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__0));
v___x_559_ = l_Lean_stringToMessageData(v___x_558_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__3(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__2));
v___x_562_ = l_Lean_stringToMessageData(v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite(lean_object* v_mvarId_563_, lean_object* v_e_564_, lean_object* v_stx_565_, uint8_t v_symm_566_, lean_object* v_config_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_st_ref_get(v_a_573_);
v___x_578_ = lean_box(0);
v___x_579_ = 1;
lean_inc(v_stx_565_);
v___x_580_ = l_Lean_Elab_Tactic_elabTerm(v_stx_565_, v___x_578_, v___x_579_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_mctx_581_; lean_object* v_a_582_; lean_object* v_mvarCounter_583_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; uint8_t v___x_649_; 
v_mctx_581_ = lean_ctor_get(v___x_577_, 0);
lean_inc_ref(v_mctx_581_);
lean_dec(v___x_577_);
v_a_582_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_582_);
lean_dec_ref(v___x_580_);
v_mvarCounter_583_ = lean_ctor_get(v_mctx_581_, 3);
lean_inc(v_mvarCounter_583_);
lean_dec_ref(v_mctx_581_);
v___x_649_ = l_Lean_Expr_hasSyntheticSorry(v_a_582_);
if (v___x_649_ == 0)
{
v___y_613_ = v_a_568_;
v___y_614_ = v_a_569_;
v___y_615_ = v_a_570_;
v___y_616_ = v_a_571_;
v___y_617_ = v_a_572_;
v___y_618_ = v_a_573_;
v___y_619_ = v_a_574_;
v___y_620_ = v_a_575_;
goto v___jp_612_;
}
else
{
lean_object* v___x_650_; lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_mvarCounter_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_config_567_);
lean_dec(v_stx_565_);
lean_dec_ref(v_e_564_);
lean_dec(v_mvarId_563_);
v___x_650_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg();
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
v___jp_584_:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_MVarId_rewrite(v_mvarId_563_, v_e_564_, v_a_582_, v_symm_566_, v_config_567_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_611_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_611_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_611_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_611_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v_mctx_595_; lean_object* v_eNew_596_; lean_object* v_eqProof_597_; lean_object* v_mvarIds_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_610_; 
v___x_594_ = lean_st_ref_get(v___y_586_);
v_mctx_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc_ref(v_mctx_595_);
lean_dec(v___x_594_);
v_eNew_596_ = lean_ctor_get(v_a_590_, 0);
v_eqProof_597_ = lean_ctor_get(v_a_590_, 1);
v_mvarIds_598_ = lean_ctor_get(v_a_590_, 2);
v_isSharedCheck_610_ = !lean_is_exclusive(v_a_590_);
if (v_isSharedCheck_610_ == 0)
{
v___x_600_ = v_a_590_;
v_isShared_601_ = v_isSharedCheck_610_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_mvarIds_598_);
lean_inc(v_eqProof_597_);
lean_inc(v_eNew_596_);
lean_dec(v_a_590_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_610_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_602_ = lean_box(0);
v___x_603_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__0(v_mctx_595_, v_mvarCounter_583_, v_mvarIds_598_, v___x_602_);
lean_dec(v_mvarCounter_583_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 2, v___x_603_);
v___x_605_ = v___x_600_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_eNew_596_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_eqProof_597_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v___x_603_);
v___x_605_ = v_reuseFailAlloc_609_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_605_);
v___x_607_ = v___x_592_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
else
{
lean_dec(v_mvarCounter_583_);
return v___x_589_;
}
}
v___jp_612_:
{
lean_object* v___x_621_; 
lean_inc(v_a_582_);
v___x_621_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v_mvarId_563_, v_a_582_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; uint8_t v___x_623_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref(v___x_621_);
v___x_623_ = lean_unbox(v_a_622_);
lean_dec(v_a_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_mvarCounter_583_);
lean_dec_ref(v_config_567_);
lean_dec_ref(v_e_564_);
v___x_624_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__1, &l_Lean_Elab_Tactic_elabRewrite___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__1);
v___x_625_ = l_Lean_indentExpr(v_a_582_);
v___x_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__3, &l_Lean_Elab_Tactic_elabRewrite___closed__3_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__3);
v___x_628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = l_Lean_Expr_mvar___override(v_mvarId_563_);
v___x_630_ = l_Lean_MessageData_ofExpr(v___x_629_);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_628_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___redArg(v_stx_565_, v___x_631_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v_stx_565_);
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
lean_dec(v_stx_565_);
v___y_585_ = v___y_617_;
v___y_586_ = v___y_618_;
v___y_587_ = v___y_619_;
v___y_588_ = v___y_620_;
goto v___jp_584_;
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v_mvarCounter_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_config_567_);
lean_dec(v_stx_565_);
lean_dec_ref(v_e_564_);
lean_dec(v_mvarId_563_);
v_a_641_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_621_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_621_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec(v___x_577_);
lean_dec_ref(v_config_567_);
lean_dec(v_stx_565_);
lean_dec_ref(v_e_564_);
lean_dec(v_mvarId_563_);
v_a_659_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_580_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_580_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___boxed(lean_object* v_mvarId_667_, lean_object* v_e_668_, lean_object* v_stx_669_, lean_object* v_symm_670_, lean_object* v_config_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
uint8_t v_symm_boxed_681_; lean_object* v_res_682_; 
v_symm_boxed_681_ = lean_unbox(v_symm_670_);
v_res_682_ = l_Lean_Elab_Tactic_elabRewrite(v_mvarId_667_, v_e_668_, v_stx_669_, v_symm_boxed_681_, v_config_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2(lean_object* v_00_u03b1_683_, lean_object* v_ref_684_, lean_object* v_msg_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___redArg(v_ref_684_, v_msg_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2___boxed(lean_object* v_00_u03b1_696_, lean_object* v_ref_697_, lean_object* v_msg_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_00_u03b1_696_, v_ref_697_, v_msg_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v_ref_697_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3(lean_object* v_00_u03b1_709_, lean_object* v_msg_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___redArg(v_msg_710_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___boxed(lean_object* v_00_u03b1_721_, lean_object* v_msg_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3(v_00_u03b1_721_, v_msg_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v_res_732_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_733_, lean_object* v_m_734_, lean_object* v_a_735_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3___redArg(v_m_734_, v_a_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_737_, lean_object* v_m_738_, lean_object* v_a_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3(v_00_u03b2_737_, v_m_738_, v_a_739_);
lean_dec_ref(v_a_739_);
lean_dec_ref(v_m_738_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_742_, lean_object* v_m_743_, lean_object* v_a_744_, lean_object* v_b_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4___redArg(v_m_743_, v_a_744_, v_b_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9(lean_object* v_mvarId_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9___redArg(v_mvarId_747_, v___y_748_, v___y_754_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9___boxed(lean_object* v_mvarId_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__9(v_mvarId_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v_mvarId_759_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10(lean_object* v_mvarId_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10___redArg(v_mvarId_771_, v___y_772_, v___y_778_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10___boxed(lean_object* v_mvarId_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__5_spec__10(v_mvarId_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v_mvarId_783_);
return v_res_794_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_795_, lean_object* v_a_796_, lean_object* v_x_797_){
_start:
{
uint8_t v___x_798_; 
v___x_798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___redArg(v_a_796_, v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_799_, lean_object* v_a_800_, lean_object* v_x_801_){
_start:
{
uint8_t v_res_802_; lean_object* v_r_803_; 
v_res_802_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_799_, v_a_800_, v_x_801_);
lean_dec(v_x_801_);
lean_dec_ref(v_a_800_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_804_, lean_object* v_data_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7___redArg(v_data_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_807_, lean_object* v_i_808_, lean_object* v_source_809_, lean_object* v_target_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10___redArg(v_i_808_, v_source_809_, v_target_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10_spec__14(lean_object* v_00_u03b2_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__1_spec__1_spec__4_spec__7_spec__10_spec__14___redArg(v_x_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(lean_object* v_mvarId_816_, lean_object* v_x_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_816_, v_x_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_a_832_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_823_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_823_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg___boxed(lean_object* v_mvarId_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_840_, v_x_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(lean_object* v_00_u03b1_848_, lean_object* v_mvarId_849_, lean_object* v_x_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_849_, v_x_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___boxed(lean_object* v_00_u03b1_857_, lean_object* v_mvarId_858_, lean_object* v_x_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(v_00_u03b1_857_, v_mvarId_858_, v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_865_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_866_, lean_object* v_i_867_, lean_object* v_k_868_){
_start:
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = lean_array_get_size(v_keys_866_);
v___x_870_ = lean_nat_dec_lt(v_i_867_, v___x_869_);
if (v___x_870_ == 0)
{
lean_dec(v_i_867_);
return v___x_870_;
}
else
{
lean_object* v_k_x27_871_; uint8_t v___x_872_; 
v_k_x27_871_ = lean_array_fget_borrowed(v_keys_866_, v_i_867_);
v___x_872_ = l_Lean_instBEqMVarId_beq(v_k_868_, v_k_x27_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(1u);
v___x_874_ = lean_nat_add(v_i_867_, v___x_873_);
lean_dec(v_i_867_);
v_i_867_ = v___x_874_;
goto _start;
}
else
{
lean_dec(v_i_867_);
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_876_, lean_object* v_i_877_, lean_object* v_k_878_){
_start:
{
uint8_t v_res_879_; lean_object* v_r_880_; 
v_res_879_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_876_, v_i_877_, v_k_878_);
lean_dec(v_k_878_);
lean_dec_ref(v_keys_876_);
v_r_880_ = lean_box(v_res_879_);
return v_r_880_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; 
v___x_881_ = ((size_t)5ULL);
v___x_882_ = ((size_t)1ULL);
v___x_883_ = lean_usize_shift_left(v___x_882_, v___x_881_);
return v___x_883_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_884_; size_t v___x_885_; size_t v___x_886_; 
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_886_ = lean_usize_sub(v___x_885_, v___x_884_);
return v___x_886_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(lean_object* v_x_887_, size_t v_x_888_, lean_object* v_x_889_){
_start:
{
if (lean_obj_tag(v_x_887_) == 0)
{
lean_object* v_es_890_; lean_object* v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v_j_895_; lean_object* v___x_896_; 
v_es_890_ = lean_ctor_get(v_x_887_, 0);
v___x_891_ = lean_box(2);
v___x_892_ = ((size_t)5ULL);
v___x_893_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_894_ = lean_usize_land(v_x_888_, v___x_893_);
v_j_895_ = lean_usize_to_nat(v___x_894_);
v___x_896_ = lean_array_get_borrowed(v___x_891_, v_es_890_, v_j_895_);
lean_dec(v_j_895_);
switch(lean_obj_tag(v___x_896_))
{
case 0:
{
lean_object* v_key_897_; uint8_t v___x_898_; 
v_key_897_ = lean_ctor_get(v___x_896_, 0);
v___x_898_ = l_Lean_instBEqMVarId_beq(v_x_889_, v_key_897_);
return v___x_898_;
}
case 1:
{
lean_object* v_node_899_; size_t v___x_900_; 
v_node_899_ = lean_ctor_get(v___x_896_, 0);
v___x_900_ = lean_usize_shift_right(v_x_888_, v___x_892_);
v_x_887_ = v_node_899_;
v_x_888_ = v___x_900_;
goto _start;
}
default: 
{
uint8_t v___x_902_; 
v___x_902_ = 0;
return v___x_902_;
}
}
}
else
{
lean_object* v_ks_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_ks_903_ = lean_ctor_get(v_x_887_, 0);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_903_, v___x_904_, v_x_889_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
size_t v_x_1971__boxed_909_; uint8_t v_res_910_; lean_object* v_r_911_; 
v_x_1971__boxed_909_ = lean_unbox_usize(v_x_907_);
lean_dec(v_x_907_);
v_res_910_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_906_, v_x_1971__boxed_909_, v_x_908_);
lean_dec(v_x_908_);
lean_dec_ref(v_x_906_);
v_r_911_ = lean_box(v_res_910_);
return v_r_911_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
uint64_t v___x_914_; size_t v___x_915_; uint8_t v___x_916_; 
v___x_914_ = l_Lean_instHashableMVarId_hash(v_x_913_);
v___x_915_ = lean_uint64_to_usize(v___x_914_);
v___x_916_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_912_, v___x_915_, v_x_913_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
uint8_t v_res_919_; lean_object* v_r_920_; 
v_res_919_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_917_, v_x_918_);
lean_dec(v_x_918_);
lean_dec_ref(v_x_917_);
v_r_920_ = lean_box(v_res_919_);
return v_r_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(lean_object* v_mvarId_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; lean_object* v_mctx_925_; lean_object* v_eAssignment_926_; uint8_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_924_ = lean_st_ref_get(v___y_922_);
v_mctx_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc_ref(v_mctx_925_);
lean_dec(v___x_924_);
v_eAssignment_926_ = lean_ctor_get(v_mctx_925_, 8);
lean_inc_ref(v_eAssignment_926_);
lean_dec_ref(v_mctx_925_);
v___x_927_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_eAssignment_926_, v_mvarId_921_);
lean_dec_ref(v_eAssignment_926_);
v___x_928_ = lean_box(v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg___boxed(lean_object* v_mvarId_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec(v_mvarId_930_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
if (lean_obj_tag(v_x_934_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v_x_935_);
return v___x_941_;
}
else
{
lean_object* v_head_942_; lean_object* v_tail_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_956_; 
v_head_942_ = lean_ctor_get(v_x_934_, 0);
v_tail_943_ = lean_ctor_get(v_x_934_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_x_934_);
if (v_isSharedCheck_956_ == 0)
{
v___x_945_ = v_x_934_;
v_isShared_946_ = v_isSharedCheck_956_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_tail_943_);
lean_inc(v_head_942_);
lean_dec(v_x_934_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_956_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_952_; lean_object* v_a_953_; uint8_t v___x_954_; 
v___x_952_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_head_942_, v___y_937_);
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref(v___x_952_);
v___x_954_ = lean_unbox(v_a_953_);
lean_dec(v_a_953_);
if (v___x_954_ == 0)
{
goto v___jp_947_;
}
else
{
lean_del_object(v___x_945_);
lean_dec(v_head_942_);
v_x_934_ = v_tail_943_;
goto _start;
}
v___jp_947_:
{
lean_object* v___x_949_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v_x_935_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_head_942_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_x_935_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
v_x_934_ = v_tail_943_;
v_x_935_ = v___x_949_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3___boxed(lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_x_957_, v_x_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(lean_object* v_head_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
lean_inc(v_head_965_);
v___x_971_ = l_Lean_MVarId_getType(v_head_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = l_Lean_Meta_isProp(v_a_972_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_985_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_985_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_985_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_985_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
uint8_t v___x_978_; 
v___x_978_ = lean_unbox(v_a_974_);
lean_dec(v_a_974_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_981_; 
lean_dec(v_head_965_);
v___x_979_ = lean_box(0);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_979_);
v___x_981_ = v___x_976_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
uint8_t v___x_983_; lean_object* v___x_984_; 
lean_del_object(v___x_976_);
v___x_983_ = 2;
v___x_984_ = l_Lean_MVarId_setKind___redArg(v_head_965_, v___x_983_, v___y_967_);
return v___x_984_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_head_965_);
v_a_986_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_973_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_973_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_head_965_);
v_a_994_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_971_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_971_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed(lean_object* v_head_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(v_head_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(lean_object* v_as_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
if (lean_obj_tag(v_as_1009_) == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
else
{
lean_object* v_head_1017_; lean_object* v_tail_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; 
v_head_1017_ = lean_ctor_get(v_as_1009_, 0);
lean_inc_n(v_head_1017_, 2);
v_tail_1018_ = lean_ctor_get(v_as_1009_, 1);
lean_inc(v_tail_1018_);
lean_dec_ref(v_as_1009_);
v___f_1019_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1019_, 0, v_head_1017_);
v___x_1020_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_head_1017_, v___f_1019_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_dec_ref(v___x_1020_);
v_as_1009_ = v_tail_1018_;
goto _start;
}
else
{
lean_dec(v_tail_1018_);
return v___x_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___boxed(lean_object* v_as_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_as_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite(lean_object* v_r_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_eNew_1035_; lean_object* v_eqProof_1036_; lean_object* v_mvarIds_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1076_; 
v_eNew_1035_ = lean_ctor_get(v_r_1029_, 0);
v_eqProof_1036_ = lean_ctor_get(v_r_1029_, 1);
v_mvarIds_1037_ = lean_ctor_get(v_r_1029_, 2);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_r_1029_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1039_ = v_r_1029_;
v_isShared_1040_ = v_isSharedCheck_1076_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_mvarIds_1037_);
lean_inc(v_eqProof_1036_);
lean_inc(v_eNew_1035_);
lean_dec(v_r_1029_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1076_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_a_1042_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_mvarIds_1037_, v___x_1063_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = l_List_reverse___redArg(v_a_1065_);
v_a_1042_ = v___x_1066_;
goto v___jp_1041_;
}
else
{
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1067_; 
v_a_1067_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1067_);
lean_dec_ref(v___x_1064_);
v_a_1042_ = v_a_1067_;
goto v___jp_1041_;
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_del_object(v___x_1039_);
lean_dec_ref(v_eqProof_1036_);
lean_dec_ref(v_eNew_1035_);
v_a_1068_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1064_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1064_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
v___jp_1041_:
{
lean_object* v___x_1043_; 
lean_inc(v_a_1042_);
v___x_1043_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_a_1042_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1053_; 
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v___x_1043_, 0);
lean_dec(v_unused_1054_);
v___x_1045_ = v___x_1043_;
v_isShared_1046_ = v_isSharedCheck_1053_;
goto v_resetjp_1044_;
}
else
{
lean_dec(v___x_1043_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1053_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 2, v_a_1042_);
v___x_1048_ = v___x_1039_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_eNew_1035_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_eqProof_1036_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_a_1042_);
v___x_1048_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1050_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1048_);
v___x_1050_ = v___x_1045_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_a_1042_);
lean_del_object(v___x_1039_);
lean_dec_ref(v_eqProof_1036_);
lean_dec_ref(v_eNew_1035_);
v_a_1055_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1043_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1043_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite___boxed(lean_object* v_r_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Elab_Tactic_finishElabRewrite(v_r_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(lean_object* v_mvarId_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1084_, v___y_1086_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___boxed(lean_object* v_mvarId_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(v_mvarId_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v_mvarId_1091_);
return v_res_1097_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(lean_object* v_00_u03b2_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
uint8_t v___x_1101_; 
v___x_1101_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1099_, v_x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
uint8_t v_res_1105_; lean_object* v_r_1106_; 
v_res_1105_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(v_00_u03b2_1102_, v_x_1103_, v_x_1104_);
lean_dec(v_x_1104_);
lean_dec_ref(v_x_1103_);
v_r_1106_ = lean_box(v_res_1105_);
return v_r_1106_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1107_, lean_object* v_x_1108_, size_t v_x_1109_, lean_object* v_x_1110_){
_start:
{
uint8_t v___x_1111_; 
v___x_1111_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1108_, v_x_1109_, v_x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
size_t v_x_2316__boxed_1116_; uint8_t v_res_1117_; lean_object* v_r_1118_; 
v_x_2316__boxed_1116_ = lean_unbox_usize(v_x_1114_);
lean_dec(v_x_1114_);
v_res_1117_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(v_00_u03b2_1112_, v_x_1113_, v_x_2316__boxed_1116_, v_x_1115_);
lean_dec(v_x_1115_);
lean_dec_ref(v_x_1113_);
v_r_1118_ = lean_box(v_res_1117_);
return v_r_1118_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1119_, lean_object* v_keys_1120_, lean_object* v_vals_1121_, lean_object* v_heq_1122_, lean_object* v_i_1123_, lean_object* v_k_1124_){
_start:
{
uint8_t v___x_1125_; 
v___x_1125_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1120_, v_i_1123_, v_k_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1126_, lean_object* v_keys_1127_, lean_object* v_vals_1128_, lean_object* v_heq_1129_, lean_object* v_i_1130_, lean_object* v_k_1131_){
_start:
{
uint8_t v_res_1132_; lean_object* v_r_1133_; 
v_res_1132_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1126_, v_keys_1127_, v_vals_1128_, v_heq_1129_, v_i_1130_, v_k_1131_);
lean_dec(v_k_1131_);
lean_dec_ref(v_vals_1128_);
lean_dec_ref(v_keys_1127_);
v_r_1133_ = lean_box(v_res_1132_);
return v_r_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object* v_stx_1134_, uint8_t v_symm_1135_, lean_object* v_config_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1138_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref(v___x_1146_);
v___x_1148_ = l_Lean_Elab_Tactic_getMainTarget(v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1150_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1147_, v_a_1149_, v_stx_1134_, v_symm_1135_, v_config_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
return v___x_1150_;
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v_a_1147_);
lean_dec_ref(v_config_1136_);
lean_dec(v_stx_1134_);
v_a_1151_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1148_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1148_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v_config_1136_);
lean_dec(v_stx_1134_);
v_a_1159_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1146_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1146_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object* v_stx_1167_, lean_object* v_symm_1168_, lean_object* v_config_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
uint8_t v_symm_boxed_1179_; lean_object* v_res_1180_; 
v_symm_boxed_1179_ = lean_unbox(v_symm_1168_);
v_res_1180_ = l_Lean_Elab_Tactic_rewriteTarget___lam__0(v_stx_1167_, v_symm_boxed_1179_, v_config_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object* v_stx_1181_, uint8_t v_symm_1182_, lean_object* v_config_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1193_; lean_object* v___f_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1193_ = lean_box(v_symm_1182_);
v___f_1194_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1194_, 0, v_stx_1181_);
lean_closure_set(v___f_1194_, 1, v___x_1193_);
lean_closure_set(v___f_1194_, 2, v_config_1183_);
v___x_1195_ = 1;
lean_inc(v_a_1185_);
lean_inc_ref(v_a_1184_);
v___x_1196_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1196_, 0, lean_box(0));
lean_closure_set(v___x_1196_, 1, v___f_1194_);
lean_closure_set(v___x_1196_, 2, v_a_1184_);
lean_closure_set(v___x_1196_, 3, v_a_1185_);
v___x_1197_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1196_, v___x_1195_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1199_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref(v___x_1197_);
v___x_1199_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1198_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1201_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1185_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v_eNew_1203_; lean_object* v_eqProof_1204_; lean_object* v_mvarIds_1205_; lean_object* v___x_1206_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref(v___x_1201_);
v_eNew_1203_ = lean_ctor_get(v_a_1200_, 0);
lean_inc_ref(v_eNew_1203_);
v_eqProof_1204_ = lean_ctor_get(v_a_1200_, 1);
lean_inc_ref(v_eqProof_1204_);
v_mvarIds_1205_ = lean_ctor_get(v_a_1200_, 2);
lean_inc(v_mvarIds_1205_);
lean_dec(v_a_1200_);
v___x_1206_ = l_Lean_MVarId_replaceTargetEq(v_a_1202_, v_eNew_1203_, v_eqProof_1204_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1206_);
v___x_1208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_a_1207_);
lean_ctor_set(v___x_1208_, 1, v_mvarIds_1205_);
v___x_1209_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1208_, v_a_1185_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
return v___x_1209_;
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v_mvarIds_1205_);
v_a_1210_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1206_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1206_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_a_1200_);
v_a_1218_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1201_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1201_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1199_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1199_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_a_1234_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1197_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1197_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object* v_stx_1242_, lean_object* v_symm_1243_, lean_object* v_config_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
uint8_t v_symm_boxed_1254_; lean_object* v_res_1255_; 
v_symm_boxed_1254_ = lean_unbox(v_symm_1243_);
v_res_1255_ = l_Lean_Elab_Tactic_rewriteTarget(v_stx_1242_, v_symm_boxed_1254_, v_config_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(lean_object* v_fvarId_1256_, lean_object* v_stx_1257_, uint8_t v_symm_1258_, lean_object* v_config_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1256_, v___y_1264_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref(v___x_1269_);
v___x_1271_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1261_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = l_Lean_LocalDecl_type(v_a_1270_);
lean_dec(v_a_1270_);
v___x_1274_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1272_, v___x_1273_, v_stx_1257_, v_symm_1258_, v_config_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
return v___x_1274_;
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_a_1270_);
lean_dec_ref(v_config_1259_);
lean_dec(v_stx_1257_);
v_a_1275_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1271_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1271_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec_ref(v_config_1259_);
lean_dec(v_stx_1257_);
v_a_1283_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1269_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1269_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed(lean_object* v_fvarId_1291_, lean_object* v_stx_1292_, lean_object* v_symm_1293_, lean_object* v_config_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v_symm_boxed_1304_; lean_object* v_res_1305_; 
v_symm_boxed_1304_ = lean_unbox(v_symm_1293_);
v_res_1305_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(v_fvarId_1291_, v_stx_1292_, v_symm_boxed_1304_, v_config_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(lean_object* v___f_1306_, uint8_t v___x_1307_, lean_object* v_fvarId_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_inc(v___y_1310_);
v___x_1318_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1318_, 0, lean_box(0));
lean_closure_set(v___x_1318_, 1, v___f_1306_);
lean_closure_set(v___x_1318_, 2, v___y_1309_);
lean_closure_set(v___x_1318_, 3, v___y_1310_);
v___x_1319_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1318_, v___x_1307_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1320_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1310_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v_eNew_1325_; lean_object* v_eqProof_1326_; lean_object* v_mvarIds_1327_; lean_object* v___x_1328_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref(v___x_1323_);
v_eNew_1325_ = lean_ctor_get(v_a_1322_, 0);
lean_inc_ref(v_eNew_1325_);
v_eqProof_1326_ = lean_ctor_get(v_a_1322_, 1);
lean_inc_ref(v_eqProof_1326_);
v_mvarIds_1327_ = lean_ctor_get(v_a_1322_, 2);
lean_inc(v_mvarIds_1327_);
lean_dec(v_a_1322_);
v___x_1328_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(v_a_1324_, v_fvarId_1308_, v_eNew_1325_, v_eqProof_1326_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v_mvarId_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref(v___x_1328_);
v_mvarId_1330_ = lean_ctor_get(v_a_1329_, 1);
lean_inc(v_mvarId_1330_);
lean_dec(v_a_1329_);
v___x_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_mvarId_1330_);
lean_ctor_set(v___x_1331_, 1, v_mvarIds_1327_);
v___x_1332_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1331_, v___y_1310_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1310_);
return v___x_1332_;
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_mvarIds_1327_);
lean_dec(v___y_1310_);
v_a_1333_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1328_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1328_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v_a_1322_);
lean_dec(v___y_1310_);
lean_dec(v_fvarId_1308_);
v_a_1341_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1323_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1323_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v___y_1310_);
lean_dec(v_fvarId_1308_);
v_a_1349_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1321_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1321_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v___y_1310_);
lean_dec(v_fvarId_1308_);
v_a_1357_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1319_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1319_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed(lean_object* v___f_1365_, lean_object* v___x_1366_, lean_object* v_fvarId_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
uint8_t v___x_1049__boxed_1377_; lean_object* v_res_1378_; 
v___x_1049__boxed_1377_ = lean_unbox(v___x_1366_);
v_res_1378_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(v___f_1365_, v___x_1049__boxed_1377_, v_fvarId_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object* v_stx_1379_, uint8_t v_symm_1380_, lean_object* v_fvarId_1381_, lean_object* v_config_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1392_; lean_object* v___f_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___f_1396_; lean_object* v___x_1397_; 
v___x_1392_ = lean_box(v_symm_1380_);
lean_inc(v_fvarId_1381_);
v___f_1393_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1393_, 0, v_fvarId_1381_);
lean_closure_set(v___f_1393_, 1, v_stx_1379_);
lean_closure_set(v___f_1393_, 2, v___x_1392_);
lean_closure_set(v___f_1393_, 3, v_config_1382_);
v___x_1394_ = 1;
v___x_1395_ = lean_box(v___x_1394_);
v___f_1396_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed), 12, 3);
lean_closure_set(v___f_1396_, 0, v___f_1393_);
lean_closure_set(v___f_1396_, 1, v___x_1395_);
lean_closure_set(v___f_1396_, 2, v_fvarId_1381_);
v___x_1397_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1396_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object* v_stx_1398_, lean_object* v_symm_1399_, lean_object* v_fvarId_1400_, lean_object* v_config_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
uint8_t v_symm_boxed_1411_; lean_object* v_res_1412_; 
v_symm_boxed_1411_ = lean_unbox(v_symm_1399_);
v_res_1412_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_stx_1398_, v_symm_boxed_1411_, v_fvarId_1400_, v_config_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
return v_res_1412_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0));
v___x_1415_ = l_Lean_stringToMessageData(v___x_1414_);
return v___x_1415_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3(void){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2));
v___x_1418_ = l_Lean_stringToMessageData(v___x_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(lean_object* v_x_1419_, uint8_t v_symm_1420_, lean_object* v_id_1421_, lean_object* v_declName_1422_, lean_object* v_hint_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
if (lean_obj_tag(v_a_1424_) == 0)
{
lean_object* v___x_1434_; uint8_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec_ref(v_x_1419_);
v___x_1434_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1);
v___x_1435_ = 0;
v___x_1436_ = l_Lean_MessageData_ofConstName(v_declName_1422_, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1434_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v_hint_1423_);
v___x_1441_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3___redArg(v___x_1440_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
return v___x_1441_;
}
else
{
lean_object* v_head_1442_; lean_object* v_tail_1443_; lean_object* v___x_1444_; 
v_head_1442_ = lean_ctor_get(v_a_1424_, 0);
lean_inc(v_head_1442_);
v_tail_1443_ = lean_ctor_get(v_a_1424_, 1);
lean_inc(v_tail_1443_);
lean_dec_ref(v_a_1424_);
v___x_1444_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1426_, v_a_1428_, v_a_1430_, v_a_1432_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; uint8_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref(v___x_1444_);
v___x_1446_ = 0;
v___x_1447_ = l_Lean_mkCIdentFrom(v_id_1421_, v_head_1442_, v___x_1446_);
v___x_1448_ = lean_box(v_symm_1420_);
lean_inc_ref(v_x_1419_);
v___x_1449_ = lean_apply_2(v_x_1419_, v___x_1448_, v___x_1447_);
v___x_1450_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_1449_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_dec(v_a_1445_);
lean_dec(v_tail_1443_);
lean_dec_ref(v_hint_1423_);
lean_dec(v_declName_1422_);
lean_dec_ref(v_x_1419_);
return v___x_1450_;
}
else
{
lean_object* v_a_1451_; uint8_t v___y_1453_; uint8_t v___x_1456_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
v___x_1456_ = l_Lean_Exception_isInterrupt(v_a_1451_);
if (v___x_1456_ == 0)
{
uint8_t v___x_1457_; 
v___x_1457_ = l_Lean_Exception_isRuntime(v_a_1451_);
v___y_1453_ = v___x_1457_;
goto v___jp_1452_;
}
else
{
lean_dec(v_a_1451_);
v___y_1453_ = v___x_1456_;
goto v___jp_1452_;
}
v___jp_1452_:
{
if (v___y_1453_ == 0)
{
lean_object* v___x_1454_; 
lean_dec_ref(v___x_1450_);
v___x_1454_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1445_, v___y_1453_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_dec_ref(v___x_1454_);
v_a_1424_ = v_tail_1443_;
goto _start;
}
else
{
lean_dec(v_tail_1443_);
lean_dec_ref(v_hint_1423_);
lean_dec(v_declName_1422_);
lean_dec_ref(v_x_1419_);
return v___x_1454_;
}
}
else
{
lean_dec(v_a_1445_);
lean_dec(v_tail_1443_);
lean_dec_ref(v_hint_1423_);
lean_dec(v_declName_1422_);
lean_dec_ref(v_x_1419_);
return v___x_1450_;
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_tail_1443_);
lean_dec(v_head_1442_);
lean_dec_ref(v_hint_1423_);
lean_dec(v_declName_1422_);
lean_dec_ref(v_x_1419_);
v_a_1458_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1444_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1444_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___boxed(lean_object* v_x_1466_, lean_object* v_symm_1467_, lean_object* v_id_1468_, lean_object* v_declName_1469_, lean_object* v_hint_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
uint8_t v_symm_boxed_1481_; lean_object* v_res_1482_; 
v_symm_boxed_1481_ = lean_unbox(v_symm_1467_);
v_res_1482_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(v_x_1466_, v_symm_boxed_1481_, v_id_1468_, v_declName_1469_, v_hint_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_id_1468_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object* v_a_1483_, lean_object* v_trees_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; 
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v___y_1488_);
lean_inc_ref(v___y_1487_);
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1485_);
v___x_1494_ = lean_apply_9(v_a_1483_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, lean_box(0));
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1503_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1499_, 0, v_a_1495_);
lean_ctor_set(v___x_1499_, 1, v_trees_1484_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1499_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec_ref(v_trees_1484_);
v_a_1504_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1494_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1494_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object* v_a_1512_, lean_object* v_trees_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(v_a_1512_, v_trees_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(lean_object* v___x_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1524_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1___boxed(lean_object* v___x_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(v___x_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(lean_object* v___y_1546_, lean_object* v_mkInfoTree_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v_a_1555_, lean_object* v_a_x3f_1556_){
_start:
{
lean_object* v___x_1558_; lean_object* v_infoState_1559_; lean_object* v_trees_1560_; lean_object* v___x_1561_; 
v___x_1558_ = lean_st_ref_get(v___y_1546_);
v_infoState_1559_ = lean_ctor_get(v___x_1558_, 7);
lean_inc_ref(v_infoState_1559_);
lean_dec(v___x_1558_);
v_trees_1560_ = lean_ctor_get(v_infoState_1559_, 2);
lean_inc_ref(v_trees_1560_);
lean_dec_ref(v_infoState_1559_);
lean_inc(v___y_1546_);
lean_inc_ref(v___y_1554_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
v___x_1561_ = lean_apply_10(v_mkInfoTree_1547_, v_trees_1560_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1546_, lean_box(0));
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1600_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1600_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1600_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v_infoState_1567_; lean_object* v_env_1568_; lean_object* v_nextMacroScope_1569_; lean_object* v_ngen_1570_; lean_object* v_auxDeclNGen_1571_; lean_object* v_traceState_1572_; lean_object* v_cache_1573_; lean_object* v_messages_1574_; lean_object* v_snapshotTasks_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1599_; 
v___x_1566_ = lean_st_ref_take(v___y_1546_);
v_infoState_1567_ = lean_ctor_get(v___x_1566_, 7);
v_env_1568_ = lean_ctor_get(v___x_1566_, 0);
v_nextMacroScope_1569_ = lean_ctor_get(v___x_1566_, 1);
v_ngen_1570_ = lean_ctor_get(v___x_1566_, 2);
v_auxDeclNGen_1571_ = lean_ctor_get(v___x_1566_, 3);
v_traceState_1572_ = lean_ctor_get(v___x_1566_, 4);
v_cache_1573_ = lean_ctor_get(v___x_1566_, 5);
v_messages_1574_ = lean_ctor_get(v___x_1566_, 6);
v_snapshotTasks_1575_ = lean_ctor_get(v___x_1566_, 8);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1577_ = v___x_1566_;
v_isShared_1578_ = v_isSharedCheck_1599_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_snapshotTasks_1575_);
lean_inc(v_infoState_1567_);
lean_inc(v_messages_1574_);
lean_inc(v_cache_1573_);
lean_inc(v_traceState_1572_);
lean_inc(v_auxDeclNGen_1571_);
lean_inc(v_ngen_1570_);
lean_inc(v_nextMacroScope_1569_);
lean_inc(v_env_1568_);
lean_dec(v___x_1566_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1599_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
uint8_t v_enabled_1579_; lean_object* v_assignment_1580_; lean_object* v_lazyAssignment_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1597_; 
v_enabled_1579_ = lean_ctor_get_uint8(v_infoState_1567_, sizeof(void*)*3);
v_assignment_1580_ = lean_ctor_get(v_infoState_1567_, 0);
v_lazyAssignment_1581_ = lean_ctor_get(v_infoState_1567_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_infoState_1567_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v_infoState_1567_, 2);
lean_dec(v_unused_1598_);
v___x_1583_ = v_infoState_1567_;
v_isShared_1584_ = v_isSharedCheck_1597_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_lazyAssignment_1581_);
lean_inc(v_assignment_1580_);
lean_dec(v_infoState_1567_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1597_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1585_ = l_Lean_PersistentArray_push___redArg(v_a_1555_, v_a_1562_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 2, v___x_1585_);
v___x_1587_ = v___x_1583_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_assignment_1580_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_lazyAssignment_1581_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v___x_1585_);
lean_ctor_set_uint8(v_reuseFailAlloc_1596_, sizeof(void*)*3, v_enabled_1579_);
v___x_1587_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1589_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 7, v___x_1587_);
v___x_1589_ = v___x_1577_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_env_1568_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_nextMacroScope_1569_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_ngen_1570_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_auxDeclNGen_1571_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_traceState_1572_);
lean_ctor_set(v_reuseFailAlloc_1595_, 5, v_cache_1573_);
lean_ctor_set(v_reuseFailAlloc_1595_, 6, v_messages_1574_);
lean_ctor_set(v_reuseFailAlloc_1595_, 7, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1595_, 8, v_snapshotTasks_1575_);
v___x_1589_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1590_ = lean_st_ref_set(v___y_1546_, v___x_1589_);
v___x_1591_ = lean_box(0);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1591_);
v___x_1593_ = v___x_1564_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v_a_1555_);
v_a_1601_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1561_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1561_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0___boxed(lean_object* v___y_1609_, lean_object* v_mkInfoTree_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v_a_1618_, lean_object* v_a_x3f_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1609_, v_mkInfoTree_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v_a_1618_, v_a_x3f_1619_);
lean_dec(v_a_x3f_1619_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1609_);
return v_res_1621_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = lean_unsigned_to_nat(32u);
v___x_1623_ = lean_mk_empty_array_with_capacity(v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
return v___x_1624_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1625_ = ((size_t)5ULL);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = lean_unsigned_to_nat(32u);
v___x_1628_ = lean_mk_empty_array_with_capacity(v___x_1627_);
v___x_1629_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0);
v___x_1630_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v___x_1628_);
lean_ctor_set(v___x_1630_, 2, v___x_1626_);
lean_ctor_set(v___x_1630_, 3, v___x_1626_);
lean_ctor_set_usize(v___x_1630_, 4, v___x_1625_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v_infoState_1634_; lean_object* v_trees_1635_; lean_object* v___x_1636_; lean_object* v_infoState_1637_; lean_object* v_env_1638_; lean_object* v_nextMacroScope_1639_; lean_object* v_ngen_1640_; lean_object* v_auxDeclNGen_1641_; lean_object* v_traceState_1642_; lean_object* v_cache_1643_; lean_object* v_messages_1644_; lean_object* v_snapshotTasks_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1666_; 
v___x_1633_ = lean_st_ref_get(v___y_1631_);
v_infoState_1634_ = lean_ctor_get(v___x_1633_, 7);
lean_inc_ref(v_infoState_1634_);
lean_dec(v___x_1633_);
v_trees_1635_ = lean_ctor_get(v_infoState_1634_, 2);
lean_inc_ref(v_trees_1635_);
lean_dec_ref(v_infoState_1634_);
v___x_1636_ = lean_st_ref_take(v___y_1631_);
v_infoState_1637_ = lean_ctor_get(v___x_1636_, 7);
v_env_1638_ = lean_ctor_get(v___x_1636_, 0);
v_nextMacroScope_1639_ = lean_ctor_get(v___x_1636_, 1);
v_ngen_1640_ = lean_ctor_get(v___x_1636_, 2);
v_auxDeclNGen_1641_ = lean_ctor_get(v___x_1636_, 3);
v_traceState_1642_ = lean_ctor_get(v___x_1636_, 4);
v_cache_1643_ = lean_ctor_get(v___x_1636_, 5);
v_messages_1644_ = lean_ctor_get(v___x_1636_, 6);
v_snapshotTasks_1645_ = lean_ctor_get(v___x_1636_, 8);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1647_ = v___x_1636_;
v_isShared_1648_ = v_isSharedCheck_1666_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_snapshotTasks_1645_);
lean_inc(v_infoState_1637_);
lean_inc(v_messages_1644_);
lean_inc(v_cache_1643_);
lean_inc(v_traceState_1642_);
lean_inc(v_auxDeclNGen_1641_);
lean_inc(v_ngen_1640_);
lean_inc(v_nextMacroScope_1639_);
lean_inc(v_env_1638_);
lean_dec(v___x_1636_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1666_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
uint8_t v_enabled_1649_; lean_object* v_assignment_1650_; lean_object* v_lazyAssignment_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1664_; 
v_enabled_1649_ = lean_ctor_get_uint8(v_infoState_1637_, sizeof(void*)*3);
v_assignment_1650_ = lean_ctor_get(v_infoState_1637_, 0);
v_lazyAssignment_1651_ = lean_ctor_get(v_infoState_1637_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_infoState_1637_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v_infoState_1637_, 2);
lean_dec(v_unused_1665_);
v___x_1653_ = v_infoState_1637_;
v_isShared_1654_ = v_isSharedCheck_1664_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_lazyAssignment_1651_);
lean_inc(v_assignment_1650_);
lean_dec(v_infoState_1637_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1664_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 2, v___x_1655_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_assignment_1650_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_lazyAssignment_1651_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v___x_1655_);
lean_ctor_set_uint8(v_reuseFailAlloc_1663_, sizeof(void*)*3, v_enabled_1649_);
v___x_1657_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 7, v___x_1657_);
v___x_1659_ = v___x_1647_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_env_1638_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_nextMacroScope_1639_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_ngen_1640_);
lean_ctor_set(v_reuseFailAlloc_1662_, 3, v_auxDeclNGen_1641_);
lean_ctor_set(v_reuseFailAlloc_1662_, 4, v_traceState_1642_);
lean_ctor_set(v_reuseFailAlloc_1662_, 5, v_cache_1643_);
lean_ctor_set(v_reuseFailAlloc_1662_, 6, v_messages_1644_);
lean_ctor_set(v_reuseFailAlloc_1662_, 7, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1662_, 8, v_snapshotTasks_1645_);
v___x_1659_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_st_ref_set(v___y_1631_, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_trees_1635_);
return v___x_1661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_1667_);
lean_dec(v___y_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(lean_object* v_x_1670_, lean_object* v_mkInfoTree_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v_infoState_1682_; uint8_t v_enabled_1683_; 
v___x_1681_ = lean_st_ref_get(v___y_1679_);
v_infoState_1682_ = lean_ctor_get(v___x_1681_, 7);
lean_inc_ref(v_infoState_1682_);
lean_dec(v___x_1681_);
v_enabled_1683_ = lean_ctor_get_uint8(v_infoState_1682_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1682_);
if (v_enabled_1683_ == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref(v_mkInfoTree_1671_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
v___x_1684_ = lean_apply_9(v_x_1670_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, lean_box(0));
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; lean_object* v_a_1686_; lean_object* v_r_1687_; 
v___x_1685_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_1679_);
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v___x_1685_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
v_r_1687_ = lean_apply_9(v_x_1670_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, lean_box(0));
if (lean_obj_tag(v_r_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1712_; 
v_a_1688_ = lean_ctor_get(v_r_1687_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_r_1687_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1690_ = v_r_1687_;
v_isShared_1691_ = v_isSharedCheck_1712_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v_r_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1712_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
lean_inc(v_a_1688_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set_tag(v___x_1690_, 1);
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1679_, v_mkInfoTree_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v_a_1686_, v___x_1693_);
lean_dec_ref(v___x_1693_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v___x_1694_, 0);
lean_dec(v_unused_1702_);
v___x_1696_ = v___x_1694_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_dec(v___x_1694_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v_a_1688_);
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1688_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_a_1688_);
v_a_1703_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1694_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1694_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_a_1713_ = lean_ctor_get(v_r_1687_, 0);
lean_inc(v_a_1713_);
lean_dec_ref(v_r_1687_);
v___x_1714_ = lean_box(0);
v___x_1715_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1679_, v_mkInfoTree_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v_a_1686_, v___x_1714_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; 
v_unused_1723_ = lean_ctor_get(v___x_1715_, 0);
lean_dec(v_unused_1723_);
v___x_1717_ = v___x_1715_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_dec(v___x_1715_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set_tag(v___x_1717_, 1);
lean_ctor_set(v___x_1717_, 0, v_a_1713_);
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1713_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v_a_1713_);
v_a_1724_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1715_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1715_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___boxed(lean_object* v_x_1732_, lean_object* v_mkInfoTree_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v_x_1732_, v_mkInfoTree_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(lean_object* v___x_1753_, uint8_t v___x_1754_, lean_object* v___x_1755_, lean_object* v_x_1756_, uint8_t v___y_1757_, lean_object* v___x_1758_, lean_object* v___x_1759_, lean_object* v___f_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_fileName_1770_; lean_object* v_fileMap_1771_; lean_object* v_options_1772_; lean_object* v_currRecDepth_1773_; lean_object* v_maxRecDepth_1774_; lean_object* v_ref_1775_; lean_object* v_currNamespace_1776_; lean_object* v_openDecls_1777_; lean_object* v_initHeartbeats_1778_; lean_object* v_maxHeartbeats_1779_; lean_object* v_quotContext_1780_; lean_object* v_currMacroScope_1781_; uint8_t v_diag_1782_; lean_object* v_cancelTk_x3f_1783_; uint8_t v_suppressElabErrors_1784_; lean_object* v_inheritedTraceOptions_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1803_; 
v_fileName_1770_ = lean_ctor_get(v___y_1767_, 0);
v_fileMap_1771_ = lean_ctor_get(v___y_1767_, 1);
v_options_1772_ = lean_ctor_get(v___y_1767_, 2);
v_currRecDepth_1773_ = lean_ctor_get(v___y_1767_, 3);
v_maxRecDepth_1774_ = lean_ctor_get(v___y_1767_, 4);
v_ref_1775_ = lean_ctor_get(v___y_1767_, 5);
v_currNamespace_1776_ = lean_ctor_get(v___y_1767_, 6);
v_openDecls_1777_ = lean_ctor_get(v___y_1767_, 7);
v_initHeartbeats_1778_ = lean_ctor_get(v___y_1767_, 8);
v_maxHeartbeats_1779_ = lean_ctor_get(v___y_1767_, 9);
v_quotContext_1780_ = lean_ctor_get(v___y_1767_, 10);
v_currMacroScope_1781_ = lean_ctor_get(v___y_1767_, 11);
v_diag_1782_ = lean_ctor_get_uint8(v___y_1767_, sizeof(void*)*14);
v_cancelTk_x3f_1783_ = lean_ctor_get(v___y_1767_, 12);
v_suppressElabErrors_1784_ = lean_ctor_get_uint8(v___y_1767_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1785_ = lean_ctor_get(v___y_1767_, 13);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___y_1767_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1787_ = v___y_1767_;
v_isShared_1788_ = v_isSharedCheck_1803_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_inheritedTraceOptions_1785_);
lean_inc(v_cancelTk_x3f_1783_);
lean_inc(v_currMacroScope_1781_);
lean_inc(v_quotContext_1780_);
lean_inc(v_maxHeartbeats_1779_);
lean_inc(v_initHeartbeats_1778_);
lean_inc(v_openDecls_1777_);
lean_inc(v_currNamespace_1776_);
lean_inc(v_ref_1775_);
lean_inc(v_maxRecDepth_1774_);
lean_inc(v_currRecDepth_1773_);
lean_inc(v_options_1772_);
lean_inc(v_fileMap_1771_);
lean_inc(v_fileName_1770_);
lean_dec(v___y_1767_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1803_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v_ref_1789_; lean_object* v___x_1791_; 
v_ref_1789_ = l_Lean_replaceRef(v___x_1753_, v_ref_1775_);
lean_dec(v_ref_1775_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 5, v_ref_1789_);
v___x_1791_ = v___x_1787_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_fileName_1770_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_fileMap_1771_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_options_1772_);
lean_ctor_set(v_reuseFailAlloc_1802_, 3, v_currRecDepth_1773_);
lean_ctor_set(v_reuseFailAlloc_1802_, 4, v_maxRecDepth_1774_);
lean_ctor_set(v_reuseFailAlloc_1802_, 5, v_ref_1789_);
lean_ctor_set(v_reuseFailAlloc_1802_, 6, v_currNamespace_1776_);
lean_ctor_set(v_reuseFailAlloc_1802_, 7, v_openDecls_1777_);
lean_ctor_set(v_reuseFailAlloc_1802_, 8, v_initHeartbeats_1778_);
lean_ctor_set(v_reuseFailAlloc_1802_, 9, v_maxHeartbeats_1779_);
lean_ctor_set(v_reuseFailAlloc_1802_, 10, v_quotContext_1780_);
lean_ctor_set(v_reuseFailAlloc_1802_, 11, v_currMacroScope_1781_);
lean_ctor_set(v_reuseFailAlloc_1802_, 12, v_cancelTk_x3f_1783_);
lean_ctor_set(v_reuseFailAlloc_1802_, 13, v_inheritedTraceOptions_1785_);
lean_ctor_set_uint8(v_reuseFailAlloc_1802_, sizeof(void*)*14, v_diag_1782_);
lean_ctor_set_uint8(v_reuseFailAlloc_1802_, sizeof(void*)*14 + 1, v_suppressElabErrors_1784_);
v___x_1791_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
if (v___x_1754_ == 0)
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4));
lean_inc(v___x_1755_);
v___x_1793_ = l_Lean_Syntax_isOfKind(v___x_1755_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec_ref(v___f_1760_);
v___x_1794_ = lean_box(v___y_1757_);
v___x_1795_ = lean_apply_11(v_x_1756_, v___x_1794_, v___x_1755_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___x_1791_, v___y_1768_, lean_box(0));
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = l_Lean_Syntax_getArg(v___x_1755_, v___x_1758_);
lean_inc(v___x_1796_);
v___x_1797_ = l_Lean_Syntax_isOfKind(v___x_1796_, v___x_1759_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec(v___x_1796_);
lean_dec_ref(v___f_1760_);
v___x_1798_ = lean_box(v___y_1757_);
v___x_1799_ = lean_apply_11(v_x_1756_, v___x_1798_, v___x_1755_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___x_1791_, v___y_1768_, lean_box(0));
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; 
lean_dec_ref(v_x_1756_);
lean_dec(v___x_1755_);
v___x_1800_ = lean_apply_10(v___f_1760_, v___x_1796_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___x_1791_, v___y_1768_, lean_box(0));
return v___x_1800_;
}
}
}
else
{
lean_object* v___x_1801_; 
lean_dec_ref(v_x_1756_);
v___x_1801_ = lean_apply_10(v___f_1760_, v___x_1755_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___x_1791_, v___y_1768_, lean_box(0));
return v___x_1801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_1804_ = _args[0];
lean_object* v___x_1805_ = _args[1];
lean_object* v___x_1806_ = _args[2];
lean_object* v_x_1807_ = _args[3];
lean_object* v___y_1808_ = _args[4];
lean_object* v___x_1809_ = _args[5];
lean_object* v___x_1810_ = _args[6];
lean_object* v___f_1811_ = _args[7];
lean_object* v___y_1812_ = _args[8];
lean_object* v___y_1813_ = _args[9];
lean_object* v___y_1814_ = _args[10];
lean_object* v___y_1815_ = _args[11];
lean_object* v___y_1816_ = _args[12];
lean_object* v___y_1817_ = _args[13];
lean_object* v___y_1818_ = _args[14];
lean_object* v___y_1819_ = _args[15];
lean_object* v___y_1820_ = _args[16];
_start:
{
uint8_t v___x_16685__boxed_1821_; uint8_t v___y_16687__boxed_1822_; lean_object* v_res_1823_; 
v___x_16685__boxed_1821_ = lean_unbox(v___x_1805_);
v___y_16687__boxed_1822_ = lean_unbox(v___y_1808_);
v_res_1823_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(v___x_1804_, v___x_16685__boxed_1821_, v___x_1806_, v_x_1807_, v___y_16687__boxed_1822_, v___x_1809_, v___x_1810_, v___f_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___x_1810_);
lean_dec(v___x_1809_);
lean_dec(v___x_1804_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(lean_object* v_a_1824_, lean_object* v_trees_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
v___x_1835_ = lean_apply_9(v_a_1824_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, lean_box(0));
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1844_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_a_1836_);
lean_ctor_set(v___x_1840_, 1, v_trees_1825_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v_trees_1825_);
v_a_1845_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1835_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1835_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object* v_a_1853_, lean_object* v_trees_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(v_a_1853_, v_trees_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(lean_object* v_id_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_Elab_Term_isLocalIdent_x3f(v_id_1865_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object* v_id_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(v_id_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
return v_res_1886_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0));
v___x_1889_ = l_Lean_stringToMessageData(v___x_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2));
v___x_1892_ = l_Lean_stringToMessageData(v___x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(lean_object* v_x_1893_, uint8_t v___y_1894_, lean_object* v___x_1895_, lean_object* v___x_1896_, lean_object* v_id_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___f_1907_; lean_object* v___x_1908_; 
lean_inc(v_id_1897_);
v___f_1907_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1907_, 0, v_id_1897_);
v___x_1908_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1907_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref(v___x_1908_);
if (lean_obj_tag(v_a_1909_) == 0)
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_1899_, v___y_1901_, v___y_1903_, v___y_1905_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1912_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1910_);
lean_inc(v_id_1897_);
v___x_1912_ = l_Lean_realizeGlobalConstNoOverload(v_id_1897_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; 
lean_dec(v_a_1911_);
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc_n(v_a_1913_, 2);
lean_dec_ref(v___x_1912_);
v___x_1914_ = l_Lean_Meta_getEqnsFor_x3f(v_a_1913_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref(v___x_1914_);
if (lean_obj_tag(v_a_1915_) == 1)
{
lean_object* v_val_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v___x_1896_);
v_val_1916_ = lean_ctor_get(v_a_1915_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_a_1915_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1918_ = v_a_1915_;
v_isShared_1919_ = v_isSharedCheck_1960_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_val_1916_);
lean_dec(v_a_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1960_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
uint8_t v___x_1920_; lean_object* v___y_1922_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1920_ = 0;
v___x_1949_ = lean_array_get_size(v_val_1916_);
v___x_1950_ = lean_nat_dec_eq(v___x_1949_, v___x_1895_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1951_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1);
v___x_1952_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_a_1913_);
v___x_1953_ = l_Lean_Name_str___override(v_a_1913_, v___x_1952_);
v___x_1954_ = l_Lean_MessageData_ofName(v___x_1953_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1951_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_MessageData_hint_x27(v___x_1957_);
v___y_1922_ = v___x_1958_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1959_; 
v___x_1959_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3);
v___y_1922_ = v___x_1959_;
goto v___jp_1921_;
}
v___jp_1921_:
{
lean_object* v___x_1923_; 
lean_inc(v_a_1913_);
v___x_1923_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_1913_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v_lctx_1925_; lean_object* v___x_1927_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref(v___x_1923_);
v_lctx_1925_ = lean_ctor_get(v___y_1902_, 2);
lean_inc_ref(v_lctx_1925_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v_lctx_1925_);
v___x_1927_ = v___x_1918_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_lctx_1925_);
v___x_1927_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_box(0);
lean_inc(v_id_1897_);
v___x_1929_ = l_Lean_Elab_Term_addTermInfo(v_id_1897_, v_a_1924_, v_a_1909_, v___x_1927_, v___x_1928_, v___x_1920_, v___x_1920_, v___x_1920_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_dec_ref(v___x_1929_);
v___x_1930_ = lean_array_to_list(v_val_1916_);
v___x_1931_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(v_x_1893_, v___y_1894_, v_id_1897_, v_a_1913_, v___y_1922_, v___x_1930_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v_id_1897_);
return v___x_1931_;
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v___y_1922_);
lean_dec(v_val_1916_);
lean_dec(v_a_1913_);
lean_dec(v_id_1897_);
lean_dec_ref(v_x_1893_);
v_a_1932_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1929_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1929_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v___y_1922_);
lean_del_object(v___x_1918_);
lean_dec(v_val_1916_);
lean_dec(v_a_1913_);
lean_dec(v_id_1897_);
lean_dec_ref(v_x_1893_);
v_a_1941_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1923_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1923_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec(v_a_1915_);
lean_dec(v_a_1913_);
lean_dec(v_id_1897_);
v___x_1961_ = lean_box(v___y_1894_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
lean_inc(v___y_1901_);
lean_inc_ref(v___y_1900_);
lean_inc(v___y_1899_);
lean_inc_ref(v___y_1898_);
v___x_1962_ = lean_apply_11(v_x_1893_, v___x_1961_, v___x_1896_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, lean_box(0));
return v___x_1962_;
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_a_1913_);
lean_dec(v_id_1897_);
lean_dec(v___x_1896_);
lean_dec_ref(v_x_1893_);
v_a_1963_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1914_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1914_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v_id_1897_);
v_a_1971_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1973_ = v___x_1912_;
v_isShared_1974_ = v_isSharedCheck_1985_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1912_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1985_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
uint8_t v___y_1976_; uint8_t v___x_1983_; 
v___x_1983_ = l_Lean_Exception_isInterrupt(v_a_1971_);
if (v___x_1983_ == 0)
{
uint8_t v___x_1984_; 
lean_inc(v_a_1971_);
v___x_1984_ = l_Lean_Exception_isRuntime(v_a_1971_);
v___y_1976_ = v___x_1984_;
goto v___jp_1975_;
}
else
{
v___y_1976_ = v___x_1983_;
goto v___jp_1975_;
}
v___jp_1975_:
{
if (v___y_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_del_object(v___x_1973_);
lean_dec(v_a_1971_);
v___x_1977_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1911_, v___y_1976_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_dec_ref(v___x_1977_);
v___x_1978_ = lean_box(v___y_1894_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
lean_inc(v___y_1901_);
lean_inc_ref(v___y_1900_);
lean_inc(v___y_1899_);
lean_inc_ref(v___y_1898_);
v___x_1979_ = lean_apply_11(v_x_1893_, v___x_1978_, v___x_1896_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, lean_box(0));
return v___x_1979_;
}
else
{
lean_dec(v___x_1896_);
lean_dec_ref(v_x_1893_);
return v___x_1977_;
}
}
else
{
lean_object* v___x_1981_; 
lean_dec(v_a_1911_);
lean_dec(v___x_1896_);
lean_dec_ref(v_x_1893_);
if (v_isShared_1974_ == 0)
{
v___x_1981_ = v___x_1973_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1971_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec(v_id_1897_);
lean_dec(v___x_1896_);
lean_dec_ref(v_x_1893_);
v_a_1986_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1910_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1910_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_dec_ref(v_a_1909_);
lean_dec(v_id_1897_);
v___x_1994_ = lean_box(v___y_1894_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
lean_inc(v___y_1901_);
lean_inc_ref(v___y_1900_);
lean_inc(v___y_1899_);
lean_inc_ref(v___y_1898_);
v___x_1995_ = lean_apply_11(v_x_1893_, v___x_1994_, v___x_1896_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, lean_box(0));
return v___x_1995_;
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v_id_1897_);
lean_dec(v___x_1896_);
lean_dec_ref(v_x_1893_);
v_a_1996_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1908_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1908_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object* v_x_2004_, lean_object* v___y_2005_, lean_object* v___x_2006_, lean_object* v___x_2007_, lean_object* v_id_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
uint8_t v___y_16885__boxed_2018_; lean_object* v_res_2019_; 
v___y_16885__boxed_2018_ = lean_unbox(v___y_2005_);
v_res_2019_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(v_x_2004_, v___y_16885__boxed_2018_, v___x_2006_, v___x_2007_, v_id_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___x_2006_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(lean_object* v_upperBound_2026_, lean_object* v_rules_2027_, lean_object* v_x_2028_, lean_object* v_a_2029_, lean_object* v_b_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
uint8_t v___x_2040_; 
v___x_2040_ = lean_nat_dec_lt(v_a_2029_, v_upperBound_2026_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; 
lean_dec(v_a_2029_);
lean_dec_ref(v_x_2028_);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v_b_2030_);
return v___x_2041_;
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2075_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2042_ = lean_unsigned_to_nat(2u);
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_unsigned_to_nat(1u);
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = lean_nat_mul(v_a_2029_, v___x_2042_);
v___x_2048_ = lean_array_get_borrowed(v___x_2043_, v_rules_2027_, v___x_2047_);
v___x_2085_ = lean_nat_add(v___x_2047_, v___x_2044_);
lean_dec(v___x_2047_);
v___x_2086_ = lean_array_get_size(v_rules_2027_);
v___x_2087_ = lean_nat_dec_lt(v___x_2085_, v___x_2086_);
if (v___x_2087_ == 0)
{
lean_dec(v___x_2085_);
v___y_2075_ = v___x_2043_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_array_fget_borrowed(v_rules_2027_, v___x_2085_);
lean_dec(v___x_2085_);
lean_inc(v___x_2088_);
v___y_2075_ = v___x_2088_;
goto v___jp_2074_;
}
v___jp_2049_:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___y_2050_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___f_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___f_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___f_2062_; lean_object* v___x_2063_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2052_);
v___f_2054_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2054_, 0, v_a_2053_);
v___x_2055_ = l_Lean_Syntax_getArg(v___x_2048_, v___x_2044_);
v___x_2056_ = lean_box(v___y_2051_);
lean_inc_n(v___x_2055_, 2);
lean_inc_ref_n(v_x_2028_, 2);
v___f_2057_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2057_, 0, v_x_2028_);
lean_closure_set(v___f_2057_, 1, v___x_2056_);
lean_closure_set(v___f_2057_, 2, v___x_2044_);
lean_closure_set(v___f_2057_, 3, v___x_2055_);
v___x_2058_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1));
v___x_2059_ = l_Lean_Syntax_isOfKind(v___x_2055_, v___x_2058_);
v___x_2060_ = lean_box(v___x_2059_);
v___x_2061_ = lean_box(v___y_2051_);
lean_inc(v___x_2048_);
v___f_2062_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed), 17, 8);
lean_closure_set(v___f_2062_, 0, v___x_2048_);
lean_closure_set(v___f_2062_, 1, v___x_2060_);
lean_closure_set(v___f_2062_, 2, v___x_2055_);
lean_closure_set(v___f_2062_, 3, v_x_2028_);
lean_closure_set(v___f_2062_, 4, v___x_2061_);
lean_closure_set(v___f_2062_, 5, v___x_2044_);
lean_closure_set(v___f_2062_, 6, v___x_2058_);
lean_closure_set(v___f_2062_, 7, v___f_2057_);
v___x_2063_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_2062_, v___f_2054_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v___x_2064_; 
lean_dec_ref(v___x_2063_);
v___x_2064_ = lean_nat_add(v_a_2029_, v___x_2044_);
lean_dec(v_a_2029_);
v_a_2029_ = v___x_2064_;
v_b_2030_ = v___x_2045_;
goto _start;
}
else
{
lean_dec(v_a_2029_);
lean_dec_ref(v_x_2028_);
return v___x_2063_;
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_a_2029_);
lean_dec_ref(v_x_2028_);
v_a_2066_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2052_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2052_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
v___jp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2076_ = lean_mk_empty_array_with_capacity(v___x_2042_);
lean_inc(v___x_2048_);
v___x_2077_ = lean_array_push(v___x_2076_, v___x_2048_);
v___x_2078_ = lean_array_push(v___x_2077_, v___y_2075_);
v___x_2079_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3));
v___x_2080_ = lean_box(2);
v___x_2081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v___x_2079_);
lean_ctor_set(v___x_2081_, 2, v___x_2078_);
v___x_2082_ = l_Lean_Syntax_getArg(v___x_2048_, v___x_2046_);
v___x_2083_ = l_Lean_Syntax_isNone(v___x_2082_);
lean_dec(v___x_2082_);
if (v___x_2083_ == 0)
{
v___y_2050_ = v___x_2081_;
v___y_2051_ = v___x_2040_;
goto v___jp_2049_;
}
else
{
uint8_t v___x_2084_; 
v___x_2084_ = 0;
v___y_2050_ = v___x_2081_;
v___y_2051_ = v___x_2084_;
goto v___jp_2049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___boxed(lean_object* v_upperBound_2089_, lean_object* v_rules_2090_, lean_object* v_x_2091_, lean_object* v_a_2092_, lean_object* v_b_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v_upperBound_2089_, v_rules_2090_, v_x_2091_, v_a_2092_, v_b_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec_ref(v_rules_2090_);
lean_dec(v_upperBound_2089_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object* v_token_2106_, lean_object* v_rwRulesSeqStx_2107_, lean_object* v_x_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v_lbrak_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2118_ = lean_unsigned_to_nat(0u);
v_lbrak_2119_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2107_, v___x_2118_);
v___x_2120_ = lean_unsigned_to_nat(2u);
v___x_2121_ = lean_mk_empty_array_with_capacity(v___x_2120_);
v___x_2122_ = lean_array_push(v___x_2121_, v_token_2106_);
v___x_2123_ = lean_array_push(v___x_2122_, v_lbrak_2119_);
v___x_2124_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3));
v___x_2125_ = lean_box(2);
v___x_2126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set(v___x_2126_, 1, v___x_2124_);
lean_ctor_set(v___x_2126_, 2, v___x_2123_);
v___x_2127_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2126_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___f_2131_; lean_object* v___x_2132_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref(v___x_2127_);
v___f_2129_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2129_, 0, v_a_2128_);
v___x_2130_ = lean_box(0);
v___f_2131_ = ((lean_object*)(l_Lean_Elab_Tactic_withRWRulesSeq___closed__0));
v___x_2132_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_2131_, v___f_2129_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v_rules_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec_ref(v___x_2132_);
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2107_, v___x_2133_);
v_rules_2135_ = l_Lean_Syntax_getArgs(v___x_2134_);
lean_dec(v___x_2134_);
v___x_2136_ = lean_array_get_size(v_rules_2135_);
v___x_2137_ = lean_nat_add(v___x_2136_, v___x_2133_);
v___x_2138_ = lean_nat_shiftr(v___x_2137_, v___x_2133_);
lean_dec(v___x_2137_);
v___x_2139_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v___x_2138_, v_rules_2135_, v_x_2108_, v___x_2118_, v___x_2130_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
lean_dec_ref(v_rules_2135_);
lean_dec(v___x_2138_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; 
v_unused_2147_ = lean_ctor_get(v___x_2139_, 0);
lean_dec(v_unused_2147_);
v___x_2141_ = v___x_2139_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_dec(v___x_2139_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___x_2130_);
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2130_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
else
{
return v___x_2139_;
}
}
else
{
lean_dec_ref(v_x_2108_);
return v___x_2132_;
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v_x_2108_);
v_a_2148_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2127_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2127_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object* v_token_2156_, lean_object* v_rwRulesSeqStx_2157_, lean_object* v_x_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_Elab_Tactic_withRWRulesSeq(v_token_2156_, v_rwRulesSeqStx_2157_, v_x_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_rwRulesSeqStx_2157_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___boxed(lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(lean_object* v_00_u03b1_2189_, lean_object* v_x_2190_, lean_object* v_mkInfoTree_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v_x_2190_, v_mkInfoTree_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___boxed(lean_object* v_00_u03b1_2202_, lean_object* v_x_2203_, lean_object* v_mkInfoTree_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(v_00_u03b1_2202_, v_x_2203_, v_mkInfoTree_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(lean_object* v_upperBound_2215_, lean_object* v_rules_2216_, lean_object* v_x_2217_, lean_object* v_inst_2218_, lean_object* v_R_2219_, lean_object* v_a_2220_, lean_object* v_b_2221_, lean_object* v_c_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v_upperBound_2215_, v_rules_2216_, v_x_2217_, v_a_2220_, v_b_2221_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2233_ = _args[0];
lean_object* v_rules_2234_ = _args[1];
lean_object* v_x_2235_ = _args[2];
lean_object* v_inst_2236_ = _args[3];
lean_object* v_R_2237_ = _args[4];
lean_object* v_a_2238_ = _args[5];
lean_object* v_b_2239_ = _args[6];
lean_object* v_c_2240_ = _args[7];
lean_object* v___y_2241_ = _args[8];
lean_object* v___y_2242_ = _args[9];
lean_object* v___y_2243_ = _args[10];
lean_object* v___y_2244_ = _args[11];
lean_object* v___y_2245_ = _args[12];
lean_object* v___y_2246_ = _args[13];
lean_object* v___y_2247_ = _args[14];
lean_object* v___y_2248_ = _args[15];
lean_object* v___y_2249_ = _args[16];
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(v_upperBound_2233_, v_rules_2234_, v_x_2235_, v_inst_2236_, v_R_2237_, v_a_2238_, v_b_2239_, v_c_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec_ref(v_rules_2234_);
lean_dec(v_upperBound_2233_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(lean_object* v_e_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v___x_2265_; uint8_t v___x_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; 
v___x_2265_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_));
v___x_2266_ = 0;
v___x_2267_ = 1;
v___x_2268_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_2265_, v_e_2259_, v___x_2266_, v___x_2267_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3____boxed(lean_object* v_e_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(v_e_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(lean_object* v_e_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(v_e_2276_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3____boxed(lean_object* v_e_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(v_e_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
return v_res_2293_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2294_; double v___x_2295_; 
v___x_2294_ = lean_unsigned_to_nat(0u);
v___x_2295_ = lean_float_of_nat(v___x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_2298_, lean_object* v_msg_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_ref_2305_; lean_object* v___x_2306_; lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2351_; 
v_ref_2305_ = lean_ctor_get(v___y_2302_, 5);
v___x_2306_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3_spec__8(v_msg_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2351_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2351_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v_traceState_2312_; lean_object* v_env_2313_; lean_object* v_nextMacroScope_2314_; lean_object* v_ngen_2315_; lean_object* v_auxDeclNGen_2316_; lean_object* v_cache_2317_; lean_object* v_messages_2318_; lean_object* v_infoState_2319_; lean_object* v_snapshotTasks_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2350_; 
v___x_2311_ = lean_st_ref_take(v___y_2303_);
v_traceState_2312_ = lean_ctor_get(v___x_2311_, 4);
v_env_2313_ = lean_ctor_get(v___x_2311_, 0);
v_nextMacroScope_2314_ = lean_ctor_get(v___x_2311_, 1);
v_ngen_2315_ = lean_ctor_get(v___x_2311_, 2);
v_auxDeclNGen_2316_ = lean_ctor_get(v___x_2311_, 3);
v_cache_2317_ = lean_ctor_get(v___x_2311_, 5);
v_messages_2318_ = lean_ctor_get(v___x_2311_, 6);
v_infoState_2319_ = lean_ctor_get(v___x_2311_, 7);
v_snapshotTasks_2320_ = lean_ctor_get(v___x_2311_, 8);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2322_ = v___x_2311_;
v_isShared_2323_ = v_isSharedCheck_2350_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_snapshotTasks_2320_);
lean_inc(v_infoState_2319_);
lean_inc(v_messages_2318_);
lean_inc(v_cache_2317_);
lean_inc(v_traceState_2312_);
lean_inc(v_auxDeclNGen_2316_);
lean_inc(v_ngen_2315_);
lean_inc(v_nextMacroScope_2314_);
lean_inc(v_env_2313_);
lean_dec(v___x_2311_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2350_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
uint64_t v_tid_2324_; lean_object* v_traces_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2349_; 
v_tid_2324_ = lean_ctor_get_uint64(v_traceState_2312_, sizeof(void*)*1);
v_traces_2325_ = lean_ctor_get(v_traceState_2312_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_traceState_2312_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2327_ = v_traceState_2312_;
v_isShared_2328_ = v_isSharedCheck_2349_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_traces_2325_);
lean_dec(v_traceState_2312_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2349_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; double v___x_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2329_ = lean_box(0);
v___x_2330_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_2331_ = 0;
v___x_2332_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2));
v___x_2333_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2333_, 0, v_cls_2298_);
lean_ctor_set(v___x_2333_, 1, v___x_2329_);
lean_ctor_set(v___x_2333_, 2, v___x_2332_);
lean_ctor_set_float(v___x_2333_, sizeof(void*)*3, v___x_2330_);
lean_ctor_set_float(v___x_2333_, sizeof(void*)*3 + 8, v___x_2330_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*3 + 16, v___x_2331_);
v___x_2334_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_2335_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v_a_2307_);
lean_ctor_set(v___x_2335_, 2, v___x_2334_);
lean_inc(v_ref_2305_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v_ref_2305_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l_Lean_PersistentArray_push___redArg(v_traces_2325_, v___x_2336_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2337_);
v___x_2339_ = v___x_2327_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2337_);
lean_ctor_set_uint64(v_reuseFailAlloc_2348_, sizeof(void*)*1, v_tid_2324_);
v___x_2339_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2341_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 4, v___x_2339_);
v___x_2341_ = v___x_2322_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_env_2313_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_nextMacroScope_2314_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_ngen_2315_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_auxDeclNGen_2316_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2347_, 5, v_cache_2317_);
lean_ctor_set(v_reuseFailAlloc_2347_, 6, v_messages_2318_);
lean_ctor_set(v_reuseFailAlloc_2347_, 7, v_infoState_2319_);
lean_ctor_set(v_reuseFailAlloc_2347_, 8, v_snapshotTasks_2320_);
v___x_2341_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2342_ = lean_st_ref_set(v___y_2303_, v___x_2341_);
v___x_2343_ = lean_box(0);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2343_);
v___x_2345_ = v___x_2309_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_2352_, lean_object* v_msg_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg(v_cls_2352_, v_msg_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2359_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_keys_2360_, lean_object* v_i_2361_, lean_object* v_k_2362_){
_start:
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = lean_array_get_size(v_keys_2360_);
v___x_2364_ = lean_nat_dec_lt(v_i_2361_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_dec(v_i_2361_);
return v___x_2364_;
}
else
{
lean_object* v_k_x27_2365_; uint8_t v___x_2366_; 
v_k_x27_2365_ = lean_array_fget_borrowed(v_keys_2360_, v_i_2361_);
v___x_2366_ = l_Lean_instBEqExtraModUse_beq(v_k_2362_, v_k_x27_2365_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = lean_nat_add(v_i_2361_, v___x_2367_);
lean_dec(v_i_2361_);
v_i_2361_ = v___x_2368_;
goto _start;
}
else
{
lean_dec(v_i_2361_);
return v___x_2366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_keys_2370_, lean_object* v_i_2371_, lean_object* v_k_2372_){
_start:
{
uint8_t v_res_2373_; lean_object* v_r_2374_; 
v_res_2373_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_keys_2370_, v_i_2371_, v_k_2372_);
lean_dec_ref(v_k_2372_);
lean_dec_ref(v_keys_2370_);
v_r_2374_ = lean_box(v_res_2373_);
return v_r_2374_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_2375_, size_t v_x_2376_, lean_object* v_x_2377_){
_start:
{
if (lean_obj_tag(v_x_2375_) == 0)
{
lean_object* v_es_2378_; lean_object* v___x_2379_; size_t v___x_2380_; size_t v___x_2381_; size_t v___x_2382_; lean_object* v_j_2383_; lean_object* v___x_2384_; 
v_es_2378_ = lean_ctor_get(v_x_2375_, 0);
v___x_2379_ = lean_box(2);
v___x_2380_ = ((size_t)5ULL);
v___x_2381_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_2382_ = lean_usize_land(v_x_2376_, v___x_2381_);
v_j_2383_ = lean_usize_to_nat(v___x_2382_);
v___x_2384_ = lean_array_get_borrowed(v___x_2379_, v_es_2378_, v_j_2383_);
lean_dec(v_j_2383_);
switch(lean_obj_tag(v___x_2384_))
{
case 0:
{
lean_object* v_key_2385_; uint8_t v___x_2386_; 
v_key_2385_ = lean_ctor_get(v___x_2384_, 0);
v___x_2386_ = l_Lean_instBEqExtraModUse_beq(v_x_2377_, v_key_2385_);
return v___x_2386_;
}
case 1:
{
lean_object* v_node_2387_; size_t v___x_2388_; 
v_node_2387_ = lean_ctor_get(v___x_2384_, 0);
v___x_2388_ = lean_usize_shift_right(v_x_2376_, v___x_2380_);
v_x_2375_ = v_node_2387_;
v_x_2376_ = v___x_2388_;
goto _start;
}
default: 
{
uint8_t v___x_2390_; 
v___x_2390_ = 0;
return v___x_2390_;
}
}
}
else
{
lean_object* v_ks_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v_ks_2391_ = lean_ctor_get(v_x_2375_, 0);
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ks_2391_, v___x_2392_, v_x_2377_);
return v___x_2393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_2394_, lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
size_t v_x_11866__boxed_2397_; uint8_t v_res_2398_; lean_object* v_r_2399_; 
v_x_11866__boxed_2397_ = lean_unbox_usize(v_x_2395_);
lean_dec(v_x_2395_);
v_res_2398_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2394_, v_x_11866__boxed_2397_, v_x_2396_);
lean_dec_ref(v_x_2396_);
lean_dec_ref(v_x_2394_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2400_, lean_object* v_x_2401_){
_start:
{
uint64_t v___x_2402_; size_t v___x_2403_; uint8_t v___x_2404_; 
v___x_2402_ = l_Lean_instHashableExtraModUse_hash(v_x_2401_);
v___x_2403_ = lean_uint64_to_usize(v___x_2402_);
v___x_2404_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2400_, v___x_2403_, v_x_2401_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2405_, lean_object* v_x_2406_){
_start:
{
uint8_t v_res_2407_; lean_object* v_r_2408_; 
v_res_2407_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg(v_x_2405_, v_x_2406_);
lean_dec_ref(v_x_2406_);
lean_dec_ref(v_x_2405_);
v_r_2408_ = lean_box(v_res_2407_);
return v_r_2408_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__1));
v___x_2412_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__0));
v___x_2413_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2412_, v___x_2411_);
return v___x_2413_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2414_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__3);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
return v___x_2416_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
return v___x_2418_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__4);
v___x_2420_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
lean_ctor_set(v___x_2420_, 2, v___x_2419_);
lean_ctor_set(v___x_2420_, 3, v___x_2419_);
lean_ctor_set(v___x_2420_, 4, v___x_2419_);
lean_ctor_set(v___x_2420_, 5, v___x_2419_);
return v___x_2420_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__9));
v___x_2426_ = l_Lean_stringToMessageData(v___x_2425_);
return v___x_2426_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__11));
v___x_2429_ = l_Lean_stringToMessageData(v___x_2428_);
return v___x_2429_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v_cls_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v_cls_2433_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__8));
v___x_2434_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__14));
v___x_2435_ = l_Lean_Name_append(v___x_2434_, v_cls_2433_);
return v___x_2435_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__17(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__16));
v___x_2438_ = l_Lean_stringToMessageData(v___x_2437_);
return v___x_2438_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__19(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__18));
v___x_2441_ = l_Lean_stringToMessageData(v___x_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0(lean_object* v_mod_2446_, uint8_t v_isMeta_2447_, lean_object* v_hint_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; lean_object* v_env_2457_; uint8_t v_isExporting_2458_; lean_object* v___x_2459_; lean_object* v_env_2460_; lean_object* v___x_2461_; lean_object* v_entry_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2456_ = lean_st_ref_get(v___y_2454_);
v_env_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc_ref(v_env_2457_);
lean_dec(v___x_2456_);
v_isExporting_2458_ = lean_ctor_get_uint8(v_env_2457_, sizeof(void*)*8);
lean_dec_ref(v_env_2457_);
v___x_2459_ = lean_st_ref_get(v___y_2454_);
v_env_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc_ref(v_env_2460_);
lean_dec(v___x_2459_);
v___x_2461_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_2446_);
v_entry_2462_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2462_, 0, v_mod_2446_);
lean_ctor_set_uint8(v_entry_2462_, sizeof(void*)*1, v_isExporting_2458_);
lean_ctor_set_uint8(v_entry_2462_, sizeof(void*)*1 + 1, v_isMeta_2447_);
v___x_2463_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2464_ = lean_box(1);
v___x_2465_ = lean_box(0);
v___x_2508_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2461_, v___x_2463_, v_env_2460_, v___x_2464_, v___x_2465_);
v___x_2509_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg(v___x_2508_, v_entry_2462_);
lean_dec(v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v_options_2510_; uint8_t v_hasTrace_2511_; 
v_options_2510_ = lean_ctor_get(v___y_2453_, 2);
v_hasTrace_2511_ = lean_ctor_get_uint8(v_options_2510_, sizeof(void*)*1);
if (v_hasTrace_2511_ == 0)
{
lean_dec(v_hint_2448_);
lean_dec(v_mod_2446_);
v___y_2467_ = v___y_2452_;
v___y_2468_ = v___y_2454_;
goto v___jp_2466_;
}
else
{
lean_object* v_inheritedTraceOptions_2512_; lean_object* v_cls_2513_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_inheritedTraceOptions_2512_ = lean_ctor_get(v___y_2453_, 13);
v_cls_2513_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__8));
v___x_2533_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__15);
v___x_2534_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2512_, v_options_2510_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_dec(v_hint_2448_);
lean_dec(v_mod_2446_);
v___y_2467_ = v___y_2452_;
v___y_2468_ = v___y_2454_;
goto v___jp_2466_;
}
else
{
lean_object* v___x_2535_; lean_object* v___y_2537_; 
v___x_2535_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__17);
if (v_isExporting_2458_ == 0)
{
lean_object* v___x_2544_; 
v___x_2544_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__22));
v___y_2537_ = v___x_2544_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__23));
v___y_2537_ = v___x_2545_;
goto v___jp_2536_;
}
v___jp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
lean_inc_ref(v___y_2537_);
v___x_2538_ = l_Lean_stringToMessageData(v___y_2537_);
v___x_2539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2535_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__19);
v___x_2541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2539_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
if (v_isMeta_2447_ == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__20));
v___y_2520_ = v___x_2541_;
v___y_2521_ = v___x_2542_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__21));
v___y_2520_ = v___x_2541_;
v___y_2521_ = v___x_2543_;
goto v___jp_2519_;
}
}
}
v___jp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___y_2515_);
lean_ctor_set(v___x_2517_, 1, v___y_2516_);
v___x_2518_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg(v_cls_2513_, v___x_2517_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_dec_ref(v___x_2518_);
v___y_2467_ = v___y_2452_;
v___y_2468_ = v___y_2454_;
goto v___jp_2466_;
}
else
{
lean_dec_ref(v_entry_2462_);
return v___x_2518_;
}
}
v___jp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
lean_inc_ref(v___y_2521_);
v___x_2522_ = l_Lean_stringToMessageData(v___y_2521_);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___y_2520_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__10);
v___x_2525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = l_Lean_MessageData_ofName(v_mod_2446_);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = l_Lean_Name_isAnonymous(v_hint_2448_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__12);
v___x_2530_ = l_Lean_MessageData_ofName(v_hint_2448_);
v___x_2531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___y_2515_ = v___x_2527_;
v___y_2516_ = v___x_2531_;
goto v___jp_2514_;
}
else
{
lean_object* v___x_2532_; 
lean_dec(v_hint_2448_);
v___x_2532_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3);
v___y_2515_ = v___x_2527_;
v___y_2516_ = v___x_2532_;
goto v___jp_2514_;
}
}
}
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec_ref(v_entry_2462_);
lean_dec(v_hint_2448_);
lean_dec(v_mod_2446_);
v___x_2546_ = lean_box(0);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
v___jp_2466_:
{
lean_object* v___x_2469_; lean_object* v_toEnvExtension_2470_; lean_object* v_env_2471_; lean_object* v_nextMacroScope_2472_; lean_object* v_ngen_2473_; lean_object* v_auxDeclNGen_2474_; lean_object* v_traceState_2475_; lean_object* v_messages_2476_; lean_object* v_infoState_2477_; lean_object* v_snapshotTasks_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2506_; 
v___x_2469_ = lean_st_ref_take(v___y_2468_);
v_toEnvExtension_2470_ = lean_ctor_get(v___x_2463_, 0);
v_env_2471_ = lean_ctor_get(v___x_2469_, 0);
v_nextMacroScope_2472_ = lean_ctor_get(v___x_2469_, 1);
v_ngen_2473_ = lean_ctor_get(v___x_2469_, 2);
v_auxDeclNGen_2474_ = lean_ctor_get(v___x_2469_, 3);
v_traceState_2475_ = lean_ctor_get(v___x_2469_, 4);
v_messages_2476_ = lean_ctor_get(v___x_2469_, 6);
v_infoState_2477_ = lean_ctor_get(v___x_2469_, 7);
v_snapshotTasks_2478_ = lean_ctor_get(v___x_2469_, 8);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2506_ == 0)
{
lean_object* v_unused_2507_; 
v_unused_2507_ = lean_ctor_get(v___x_2469_, 5);
lean_dec(v_unused_2507_);
v___x_2480_ = v___x_2469_;
v_isShared_2481_ = v_isSharedCheck_2506_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_snapshotTasks_2478_);
lean_inc(v_infoState_2477_);
lean_inc(v_messages_2476_);
lean_inc(v_traceState_2475_);
lean_inc(v_auxDeclNGen_2474_);
lean_inc(v_ngen_2473_);
lean_inc(v_nextMacroScope_2472_);
lean_inc(v_env_2471_);
lean_dec(v___x_2469_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2506_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_asyncMode_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; 
v_asyncMode_2482_ = lean_ctor_get(v_toEnvExtension_2470_, 2);
v___x_2483_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2463_, v_env_2471_, v_entry_2462_, v_asyncMode_2482_, v___x_2465_);
v___x_2484_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__5);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 5, v___x_2484_);
lean_ctor_set(v___x_2480_, 0, v___x_2483_);
v___x_2486_ = v___x_2480_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_nextMacroScope_2472_);
lean_ctor_set(v_reuseFailAlloc_2505_, 2, v_ngen_2473_);
lean_ctor_set(v_reuseFailAlloc_2505_, 3, v_auxDeclNGen_2474_);
lean_ctor_set(v_reuseFailAlloc_2505_, 4, v_traceState_2475_);
lean_ctor_set(v_reuseFailAlloc_2505_, 5, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2505_, 6, v_messages_2476_);
lean_ctor_set(v_reuseFailAlloc_2505_, 7, v_infoState_2477_);
lean_ctor_set(v_reuseFailAlloc_2505_, 8, v_snapshotTasks_2478_);
v___x_2486_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_mctx_2489_; lean_object* v_zetaDeltaFVarIds_2490_; lean_object* v_postponed_2491_; lean_object* v_diag_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2503_; 
v___x_2487_ = lean_st_ref_set(v___y_2468_, v___x_2486_);
v___x_2488_ = lean_st_ref_take(v___y_2467_);
v_mctx_2489_ = lean_ctor_get(v___x_2488_, 0);
v_zetaDeltaFVarIds_2490_ = lean_ctor_get(v___x_2488_, 2);
v_postponed_2491_ = lean_ctor_get(v___x_2488_, 3);
v_diag_2492_ = lean_ctor_get(v___x_2488_, 4);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; 
v_unused_2504_ = lean_ctor_get(v___x_2488_, 1);
lean_dec(v_unused_2504_);
v___x_2494_ = v___x_2488_;
v_isShared_2495_ = v_isSharedCheck_2503_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_diag_2492_);
lean_inc(v_postponed_2491_);
lean_inc(v_zetaDeltaFVarIds_2490_);
lean_inc(v_mctx_2489_);
lean_dec(v___x_2488_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2503_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2496_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___closed__6);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 1, v___x_2496_);
v___x_2498_ = v___x_2494_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_mctx_2489_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_zetaDeltaFVarIds_2490_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v_postponed_2491_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v_diag_2492_);
v___x_2498_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_st_ref_set(v___y_2467_, v___x_2498_);
v___x_2500_ = lean_box(0);
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0___boxed(lean_object* v_mod_2548_, lean_object* v_isMeta_2549_, lean_object* v_hint_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
uint8_t v_isMeta_boxed_2558_; lean_object* v_res_2559_; 
v_isMeta_boxed_2558_ = lean_unbox(v_isMeta_2549_);
v_res_2559_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0(v_mod_2548_, v_isMeta_boxed_2558_, v_hint_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1(lean_object* v___x_2560_, lean_object* v_declName_2561_, lean_object* v_as_2562_, size_t v_sz_2563_, size_t v_i_2564_, lean_object* v_b_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
uint8_t v___x_2573_; 
v___x_2573_ = lean_usize_dec_lt(v_i_2564_, v_sz_2563_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; 
lean_dec(v_declName_2561_);
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v_b_2565_);
return v___x_2574_;
}
else
{
lean_object* v___x_2575_; lean_object* v_modules_2576_; lean_object* v___x_2577_; lean_object* v_a_2578_; lean_object* v___x_2579_; lean_object* v_toImport_2580_; lean_object* v_module_2581_; uint8_t v___x_2582_; lean_object* v___x_2583_; 
v___x_2575_ = l_Lean_Environment_header(v___x_2560_);
v_modules_2576_ = lean_ctor_get(v___x_2575_, 3);
lean_inc_ref(v_modules_2576_);
lean_dec_ref(v___x_2575_);
v___x_2577_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2578_ = lean_array_uget_borrowed(v_as_2562_, v_i_2564_);
v___x_2579_ = lean_array_get(v___x_2577_, v_modules_2576_, v_a_2578_);
lean_dec_ref(v_modules_2576_);
v_toImport_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc_ref(v_toImport_2580_);
lean_dec(v___x_2579_);
v_module_2581_ = lean_ctor_get(v_toImport_2580_, 0);
lean_inc(v_module_2581_);
lean_dec_ref(v_toImport_2580_);
v___x_2582_ = 0;
lean_inc(v_declName_2561_);
v___x_2583_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0(v_module_2581_, v___x_2582_, v_declName_2561_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2584_; size_t v___x_2585_; size_t v___x_2586_; 
lean_dec_ref(v___x_2583_);
v___x_2584_ = lean_box(0);
v___x_2585_ = ((size_t)1ULL);
v___x_2586_ = lean_usize_add(v_i_2564_, v___x_2585_);
v_i_2564_ = v___x_2586_;
v_b_2565_ = v___x_2584_;
goto _start;
}
else
{
lean_dec(v_declName_2561_);
return v___x_2583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1___boxed(lean_object* v___x_2588_, lean_object* v_declName_2589_, lean_object* v_as_2590_, lean_object* v_sz_2591_, lean_object* v_i_2592_, lean_object* v_b_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
size_t v_sz_boxed_2601_; size_t v_i_boxed_2602_; lean_object* v_res_2603_; 
v_sz_boxed_2601_ = lean_unbox_usize(v_sz_2591_);
lean_dec(v_sz_2591_);
v_i_boxed_2602_ = lean_unbox_usize(v_i_2592_);
lean_dec(v_i_2592_);
v_res_2603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1(v___x_2588_, v_declName_2589_, v_as_2590_, v_sz_boxed_2601_, v_i_boxed_2602_, v_b_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec_ref(v_as_2590_);
lean_dec_ref(v___x_2588_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5___redArg(lean_object* v_a_2604_, lean_object* v_x_2605_){
_start:
{
if (lean_obj_tag(v_x_2605_) == 0)
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_box(0);
return v___x_2606_;
}
else
{
lean_object* v_key_2607_; lean_object* v_value_2608_; lean_object* v_tail_2609_; uint8_t v___x_2610_; 
v_key_2607_ = lean_ctor_get(v_x_2605_, 0);
v_value_2608_ = lean_ctor_get(v_x_2605_, 1);
v_tail_2609_ = lean_ctor_get(v_x_2605_, 2);
v___x_2610_ = lean_name_eq(v_key_2607_, v_a_2604_);
if (v___x_2610_ == 0)
{
v_x_2605_ = v_tail_2609_;
goto _start;
}
else
{
lean_object* v___x_2612_; 
lean_inc(v_value_2608_);
v___x_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2612_, 0, v_value_2608_);
return v___x_2612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2613_, lean_object* v_x_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5___redArg(v_a_2613_, v_x_2614_);
lean_dec(v_x_2614_);
lean_dec(v_a_2613_);
return v_res_2615_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2616_; uint64_t v___x_2617_; 
v___x_2616_ = lean_unsigned_to_nat(1723u);
v___x_2617_ = lean_uint64_of_nat(v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg(lean_object* v_m_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v_buckets_2620_; lean_object* v___x_2621_; uint64_t v___y_2623_; 
v_buckets_2620_ = lean_ctor_get(v_m_2618_, 1);
v___x_2621_ = lean_array_get_size(v_buckets_2620_);
if (lean_obj_tag(v_a_2619_) == 0)
{
uint64_t v___x_2637_; 
v___x_2637_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___closed__0);
v___y_2623_ = v___x_2637_;
goto v___jp_2622_;
}
else
{
uint64_t v_hash_2638_; 
v_hash_2638_ = lean_ctor_get_uint64(v_a_2619_, sizeof(void*)*2);
v___y_2623_ = v_hash_2638_;
goto v___jp_2622_;
}
v___jp_2622_:
{
uint64_t v___x_2624_; uint64_t v___x_2625_; uint64_t v_fold_2626_; uint64_t v___x_2627_; uint64_t v___x_2628_; uint64_t v___x_2629_; size_t v___x_2630_; size_t v___x_2631_; size_t v___x_2632_; size_t v___x_2633_; size_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2624_ = 32ULL;
v___x_2625_ = lean_uint64_shift_right(v___y_2623_, v___x_2624_);
v_fold_2626_ = lean_uint64_xor(v___y_2623_, v___x_2625_);
v___x_2627_ = 16ULL;
v___x_2628_ = lean_uint64_shift_right(v_fold_2626_, v___x_2627_);
v___x_2629_ = lean_uint64_xor(v_fold_2626_, v___x_2628_);
v___x_2630_ = lean_uint64_to_usize(v___x_2629_);
v___x_2631_ = lean_usize_of_nat(v___x_2621_);
v___x_2632_ = ((size_t)1ULL);
v___x_2633_ = lean_usize_sub(v___x_2631_, v___x_2632_);
v___x_2634_ = lean_usize_land(v___x_2630_, v___x_2633_);
v___x_2635_ = lean_array_uget_borrowed(v_buckets_2620_, v___x_2634_);
v___x_2636_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5___redArg(v_a_2619_, v___x_2635_);
return v___x_2636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg(v_m_2639_, v_a_2640_);
lean_dec(v_a_2640_);
lean_dec_ref(v_m_2639_);
return v_res_2641_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2644_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__1));
v___x_2645_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__0));
v___x_2646_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2645_, v___x_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0(lean_object* v_declName_2649_, uint8_t v_isMeta_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2658_; lean_object* v_env_2662_; lean_object* v___y_2664_; lean_object* v___x_2677_; 
v___x_2658_ = lean_st_ref_get(v___y_2656_);
v_env_2662_ = lean_ctor_get(v___x_2658_, 0);
lean_inc_ref(v_env_2662_);
lean_dec(v___x_2658_);
v___x_2677_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2662_, v_declName_2649_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_dec_ref(v_env_2662_);
lean_dec(v_declName_2649_);
goto v___jp_2659_;
}
else
{
lean_object* v_val_2678_; lean_object* v___x_2679_; lean_object* v_modules_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v_val_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_val_2678_);
lean_dec_ref(v___x_2677_);
v___x_2679_ = l_Lean_Environment_header(v_env_2662_);
v_modules_2680_ = lean_ctor_get(v___x_2679_, 3);
lean_inc_ref(v_modules_2680_);
lean_dec_ref(v___x_2679_);
v___x_2681_ = lean_array_get_size(v_modules_2680_);
v___x_2682_ = lean_nat_dec_lt(v_val_2678_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_dec_ref(v_modules_2680_);
lean_dec(v_val_2678_);
lean_dec_ref(v_env_2662_);
lean_dec(v_declName_2649_);
goto v___jp_2659_;
}
else
{
lean_object* v___x_2683_; lean_object* v_env_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___y_2688_; 
v___x_2683_ = lean_st_ref_get(v___y_2656_);
v_env_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc_ref(v_env_2684_);
lean_dec(v___x_2683_);
v___x_2685_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__2);
v___x_2686_ = lean_array_fget(v_modules_2680_, v_val_2678_);
lean_dec(v_val_2678_);
lean_dec_ref(v_modules_2680_);
if (v_isMeta_2650_ == 0)
{
lean_dec_ref(v_env_2684_);
v___y_2688_ = v_isMeta_2650_;
goto v___jp_2687_;
}
else
{
uint8_t v___x_2699_; 
lean_inc(v_declName_2649_);
v___x_2699_ = l_Lean_isMarkedMeta(v_env_2684_, v_declName_2649_);
if (v___x_2699_ == 0)
{
v___y_2688_ = v_isMeta_2650_;
goto v___jp_2687_;
}
else
{
uint8_t v___x_2700_; 
v___x_2700_ = 0;
v___y_2688_ = v___x_2700_;
goto v___jp_2687_;
}
}
v___jp_2687_:
{
lean_object* v_toImport_2689_; lean_object* v_module_2690_; lean_object* v___x_2691_; 
v_toImport_2689_ = lean_ctor_get(v___x_2686_, 0);
lean_inc_ref(v_toImport_2689_);
lean_dec(v___x_2686_);
v_module_2690_ = lean_ctor_get(v_toImport_2689_, 0);
lean_inc(v_module_2690_);
lean_dec_ref(v_toImport_2689_);
lean_inc(v_declName_2649_);
v___x_2691_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0(v_module_2690_, v___y_2688_, v_declName_2649_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_dec_ref(v___x_2691_);
v___x_2692_ = l_Lean_indirectModUseExt;
v___x_2693_ = lean_box(1);
v___x_2694_ = lean_box(0);
lean_inc_ref(v_env_2662_);
v___x_2695_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2685_, v___x_2692_, v_env_2662_, v___x_2693_, v___x_2694_);
v___x_2696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg(v___x_2695_, v_declName_2649_);
lean_dec(v___x_2695_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v___x_2697_; 
v___x_2697_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___closed__3));
v___y_2664_ = v___x_2697_;
goto v___jp_2663_;
}
else
{
lean_object* v_val_2698_; 
v_val_2698_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_val_2698_);
lean_dec_ref(v___x_2696_);
v___y_2664_ = v_val_2698_;
goto v___jp_2663_;
}
}
else
{
lean_dec_ref(v_env_2662_);
lean_dec(v_declName_2649_);
return v___x_2691_;
}
}
}
}
v___jp_2659_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_box(0);
v___x_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
return v___x_2661_;
}
v___jp_2663_:
{
lean_object* v___x_2665_; size_t v_sz_2666_; size_t v___x_2667_; lean_object* v___x_2668_; 
v___x_2665_ = lean_box(0);
v_sz_2666_ = lean_array_size(v___y_2664_);
v___x_2667_ = ((size_t)0ULL);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__1(v_env_2662_, v_declName_2649_, v___y_2664_, v_sz_2666_, v___x_2667_, v___x_2665_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec_ref(v___y_2664_);
lean_dec_ref(v_env_2662_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; 
v_unused_2676_ = lean_ctor_get(v___x_2668_, 0);
lean_dec(v_unused_2676_);
v___x_2670_ = v___x_2668_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_dec(v___x_2668_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2665_);
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2665_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
else
{
return v___x_2668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0___boxed(lean_object* v_declName_2701_, lean_object* v_isMeta_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
uint8_t v_isMeta_boxed_2710_; lean_object* v_res_2711_; 
v_isMeta_boxed_2710_ = lean_unbox(v_isMeta_2702_);
v_res_2711_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0(v_declName_2701_, v_isMeta_boxed_2710_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2711_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = lean_box(1);
v___x_2713_ = l_Lean_MessageData_ofFormat(v___x_2712_);
return v___x_2713_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__2));
v___x_2718_ = l_Lean_MessageData_ofFormat(v___x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9(lean_object* v_x_2719_, lean_object* v_x_2720_){
_start:
{
if (lean_obj_tag(v_x_2720_) == 0)
{
return v_x_2719_;
}
else
{
lean_object* v_head_2721_; lean_object* v_tail_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2744_; 
v_head_2721_ = lean_ctor_get(v_x_2720_, 0);
v_tail_2722_ = lean_ctor_get(v_x_2720_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_x_2720_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2724_ = v_x_2720_;
v_isShared_2725_ = v_isSharedCheck_2744_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_tail_2722_);
lean_inc(v_head_2721_);
lean_dec(v_x_2720_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2744_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_before_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2742_; 
v_before_2726_ = lean_ctor_get(v_head_2721_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_head_2721_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; 
v_unused_2743_ = lean_ctor_get(v_head_2721_, 1);
lean_dec(v_unused_2743_);
v___x_2728_ = v_head_2721_;
v_isShared_2729_ = v_isSharedCheck_2742_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_before_2726_);
lean_dec(v_head_2721_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2742_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2730_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__0);
if (v_isShared_2729_ == 0)
{
lean_ctor_set_tag(v___x_2728_, 7);
lean_ctor_set(v___x_2728_, 1, v___x_2730_);
lean_ctor_set(v___x_2728_, 0, v_x_2719_);
v___x_2732_ = v___x_2728_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_x_2719_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2733_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__3);
if (v_isShared_2725_ == 0)
{
lean_ctor_set_tag(v___x_2724_, 7);
lean_ctor_set(v___x_2724_, 1, v___x_2733_);
lean_ctor_set(v___x_2724_, 0, v___x_2732_);
v___x_2735_ = v___x_2724_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2732_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = l_Lean_MessageData_ofSyntax(v_before_2726_);
v___x_2737_ = l_Lean_indentD(v___x_2736_);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2735_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v_x_2719_ = v___x_2738_;
v_x_2720_ = v_tail_2722_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__8(lean_object* v_opts_2745_, lean_object* v_opt_2746_){
_start:
{
lean_object* v_name_2747_; lean_object* v_defValue_2748_; lean_object* v_map_2749_; lean_object* v___x_2750_; 
v_name_2747_ = lean_ctor_get(v_opt_2746_, 0);
v_defValue_2748_ = lean_ctor_get(v_opt_2746_, 1);
v_map_2749_ = lean_ctor_get(v_opts_2745_, 0);
v___x_2750_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2749_, v_name_2747_);
if (lean_obj_tag(v___x_2750_) == 0)
{
uint8_t v___x_2751_; 
v___x_2751_ = lean_unbox(v_defValue_2748_);
return v___x_2751_;
}
else
{
lean_object* v_val_2752_; 
v_val_2752_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_val_2752_);
lean_dec_ref(v___x_2750_);
if (lean_obj_tag(v_val_2752_) == 1)
{
uint8_t v_v_2753_; 
v_v_2753_ = lean_ctor_get_uint8(v_val_2752_, 0);
lean_dec_ref(v_val_2752_);
return v_v_2753_;
}
else
{
uint8_t v___x_2754_; 
lean_dec(v_val_2752_);
v___x_2754_ = lean_unbox(v_defValue_2748_);
return v___x_2754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__8___boxed(lean_object* v_opts_2755_, lean_object* v_opt_2756_){
_start:
{
uint8_t v_res_2757_; lean_object* v_r_2758_; 
v_res_2757_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__8(v_opts_2755_, v_opt_2756_);
lean_dec_ref(v_opt_2756_);
lean_dec_ref(v_opts_2755_);
v_r_2758_ = lean_box(v_res_2757_);
return v_r_2758_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__1));
v___x_2763_ = l_Lean_MessageData_ofFormat(v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg(lean_object* v_msgData_2764_, lean_object* v_macroStack_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_options_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v_options_2768_ = lean_ctor_get(v___y_2766_, 2);
v___x_2769_ = l_Lean_Elab_pp_macroStack;
v___x_2770_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__8(v_options_2768_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; 
lean_dec(v_macroStack_2765_);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_msgData_2764_);
return v___x_2771_;
}
else
{
if (lean_obj_tag(v_macroStack_2765_) == 0)
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_msgData_2764_);
return v___x_2772_;
}
else
{
lean_object* v_head_2773_; lean_object* v_after_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2789_; 
v_head_2773_ = lean_ctor_get(v_macroStack_2765_, 0);
lean_inc(v_head_2773_);
v_after_2774_ = lean_ctor_get(v_head_2773_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_head_2773_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v_head_2773_, 0);
lean_dec(v_unused_2790_);
v___x_2776_ = v_head_2773_;
v_isShared_2777_ = v_isSharedCheck_2789_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_after_2774_);
lean_dec(v_head_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2789_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v___x_2780_; 
v___x_2778_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9___closed__0);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 7);
lean_ctor_set(v___x_2776_, 1, v___x_2778_);
lean_ctor_set(v___x_2776_, 0, v_msgData_2764_);
v___x_2780_ = v___x_2776_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_msgData_2764_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v_msgData_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2781_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___closed__2);
v___x_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = l_Lean_MessageData_ofSyntax(v_after_2774_);
v___x_2784_ = l_Lean_indentD(v___x_2783_);
v_msgData_2785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2785_, 0, v___x_2782_);
lean_ctor_set(v_msgData_2785_, 1, v___x_2784_);
v___x_2786_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4_spec__9(v_msgData_2785_, v_macroStack_2765_);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
return v___x_2787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_2791_, lean_object* v_macroStack_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg(v_msgData_2791_, v_macroStack_2792_, v___y_2793_);
lean_dec_ref(v___y_2793_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(lean_object* v_msg_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_ref_2804_; lean_object* v___x_2805_; lean_object* v_a_2806_; lean_object* v_macroStack_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2818_; 
v_ref_2804_ = lean_ctor_get(v___y_2801_, 5);
v___x_2805_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__3_spec__8(v_msg_2796_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref(v___x_2805_);
v_macroStack_2807_ = lean_ctor_get(v___y_2797_, 1);
lean_inc_n(v_macroStack_2807_, 2);
v___x_2808_ = l_Lean_Elab_getBetterRef(v_ref_2804_, v_macroStack_2807_);
v___x_2809_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg(v_a_2806_, v_macroStack_2807_, v___y_2801_);
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2818_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2818_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v___x_2816_; 
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2808_);
lean_ctor_set(v___x_2814_, 1, v_a_2810_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set_tag(v___x_2812_, 1);
lean_ctor_set(v___x_2812_, 0, v___x_2814_);
v___x_2816_ = v___x_2812_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg___boxed(lean_object* v_msg_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(v_msg_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
return v_res_2827_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0));
v___x_2830_ = l_Lean_stringToMessageData(v___x_2829_);
return v___x_2830_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__2));
v___x_2833_ = l_Lean_stringToMessageData(v___x_2832_);
return v___x_2833_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__4));
v___x_2836_ = l_Lean_stringToMessageData(v___x_2835_);
return v___x_2836_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__7));
v___x_2844_ = l_Lean_stringToMessageData(v___x_2843_);
return v___x_2844_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_));
v___x_2846_ = l_Lean_MessageData_ofName(v___x_2845_);
return v___x_2846_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__10(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__9, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__9);
v___x_2848_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__8, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__8);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set(v___x_2849_, 1, v___x_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object* v_optConfig_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; uint8_t v___y_2869_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; uint8_t v_recover_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; uint8_t v___x_2897_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; 
v_recover_2891_ = lean_ctor_get_uint8(v_a_2851_, sizeof(void*)*1);
lean_inc(v_optConfig_2850_);
v___x_2892_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_2850_);
v___x_2893_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_2892_);
v___x_2894_ = lean_array_get_size(v___x_2893_);
v___x_2895_ = lean_unsigned_to_nat(0u);
v___x_2896_ = lean_nat_dec_eq(v___x_2894_, v___x_2895_);
v___x_2897_ = 1;
if (v___x_2896_ == 0)
{
lean_object* v___x_2945_; lean_object* v_fileName_2946_; lean_object* v_fileMap_2947_; lean_object* v_options_2948_; lean_object* v_currRecDepth_2949_; lean_object* v_maxRecDepth_2950_; lean_object* v_ref_2951_; lean_object* v_currNamespace_2952_; lean_object* v_openDecls_2953_; lean_object* v_initHeartbeats_2954_; lean_object* v_maxHeartbeats_2955_; lean_object* v_quotContext_2956_; lean_object* v_currMacroScope_2957_; uint8_t v_diag_2958_; lean_object* v_cancelTk_x3f_2959_; uint8_t v_suppressElabErrors_2960_; lean_object* v_inheritedTraceOptions_2961_; lean_object* v_env_2962_; lean_object* v_ref_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2945_ = lean_st_ref_get(v_a_2857_);
v_fileName_2946_ = lean_ctor_get(v_a_2856_, 0);
v_fileMap_2947_ = lean_ctor_get(v_a_2856_, 1);
v_options_2948_ = lean_ctor_get(v_a_2856_, 2);
v_currRecDepth_2949_ = lean_ctor_get(v_a_2856_, 3);
v_maxRecDepth_2950_ = lean_ctor_get(v_a_2856_, 4);
v_ref_2951_ = lean_ctor_get(v_a_2856_, 5);
v_currNamespace_2952_ = lean_ctor_get(v_a_2856_, 6);
v_openDecls_2953_ = lean_ctor_get(v_a_2856_, 7);
v_initHeartbeats_2954_ = lean_ctor_get(v_a_2856_, 8);
v_maxHeartbeats_2955_ = lean_ctor_get(v_a_2856_, 9);
v_quotContext_2956_ = lean_ctor_get(v_a_2856_, 10);
v_currMacroScope_2957_ = lean_ctor_get(v_a_2856_, 11);
v_diag_2958_ = lean_ctor_get_uint8(v_a_2856_, sizeof(void*)*14);
v_cancelTk_x3f_2959_ = lean_ctor_get(v_a_2856_, 12);
v_suppressElabErrors_2960_ = lean_ctor_get_uint8(v_a_2856_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2961_ = lean_ctor_get(v_a_2856_, 13);
v_env_2962_ = lean_ctor_get(v___x_2945_, 0);
lean_inc_ref(v_env_2962_);
lean_dec(v___x_2945_);
v_ref_2963_ = l_Lean_replaceRef(v_optConfig_2850_, v_ref_2951_);
lean_dec(v_optConfig_2850_);
lean_inc_ref(v_inheritedTraceOptions_2961_);
lean_inc(v_cancelTk_x3f_2959_);
lean_inc(v_currMacroScope_2957_);
lean_inc(v_quotContext_2956_);
lean_inc(v_maxHeartbeats_2955_);
lean_inc(v_initHeartbeats_2954_);
lean_inc(v_openDecls_2953_);
lean_inc(v_currNamespace_2952_);
lean_inc(v_maxRecDepth_2950_);
lean_inc(v_currRecDepth_2949_);
lean_inc_ref(v_options_2948_);
lean_inc_ref(v_fileMap_2947_);
lean_inc_ref(v_fileName_2946_);
v___x_2964_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2964_, 0, v_fileName_2946_);
lean_ctor_set(v___x_2964_, 1, v_fileMap_2947_);
lean_ctor_set(v___x_2964_, 2, v_options_2948_);
lean_ctor_set(v___x_2964_, 3, v_currRecDepth_2949_);
lean_ctor_set(v___x_2964_, 4, v_maxRecDepth_2950_);
lean_ctor_set(v___x_2964_, 5, v_ref_2963_);
lean_ctor_set(v___x_2964_, 6, v_currNamespace_2952_);
lean_ctor_set(v___x_2964_, 7, v_openDecls_2953_);
lean_ctor_set(v___x_2964_, 8, v_initHeartbeats_2954_);
lean_ctor_set(v___x_2964_, 9, v_maxHeartbeats_2955_);
lean_ctor_set(v___x_2964_, 10, v_quotContext_2956_);
lean_ctor_set(v___x_2964_, 11, v_currMacroScope_2957_);
lean_ctor_set(v___x_2964_, 12, v_cancelTk_x3f_2959_);
lean_ctor_set(v___x_2964_, 13, v_inheritedTraceOptions_2961_);
lean_ctor_set_uint8(v___x_2964_, sizeof(void*)*14, v_diag_2958_);
lean_ctor_set_uint8(v___x_2964_, sizeof(void*)*14 + 1, v_suppressElabErrors_2960_);
v___x_2965_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_));
v___x_2966_ = l_Lean_Environment_contains(v_env_2962_, v___x_2965_, v___x_2897_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec_ref(v___x_2893_);
v___x_2967_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__10, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__10_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__10);
v___x_2968_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(v___x_2967_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v___x_2964_, v_a_2857_);
lean_dec_ref(v___x_2964_);
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2968_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
else
{
v___y_2899_ = v_a_2852_;
v___y_2900_ = v_a_2853_;
v___y_2901_ = v_a_2854_;
v___y_2902_ = v_a_2855_;
v___y_2903_ = v___x_2964_;
v___y_2904_ = v_a_2857_;
goto v___jp_2898_;
}
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec_ref(v___x_2893_);
lean_dec(v_optConfig_2850_);
v___x_2977_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__6));
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
v___jp_2859_:
{
if (v___y_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
lean_dec_ref(v___y_2863_);
v___x_2870_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__1, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__1);
v___x_2871_ = l_Lean_MessageData_ofExpr(v___y_2866_);
v___x_2872_ = l_Lean_indentD(v___x_2871_);
v___x_2873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2870_);
lean_ctor_set(v___x_2873_, 1, v___x_2872_);
v___x_2874_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__3, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__3);
v___x_2875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = l_Lean_Exception_toMessageData(v___y_2861_);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(v___x_2877_, v___y_2865_, v___y_2862_, v___y_2868_, v___y_2864_, v___y_2867_, v___y_2860_);
lean_dec_ref(v___y_2867_);
return v___x_2878_;
}
else
{
lean_dec_ref(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec_ref(v___y_2861_);
return v___y_2863_;
}
}
v___jp_2879_:
{
lean_object* v___x_2887_; 
lean_inc_ref(v___y_2880_);
v___x_2887_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_(v___y_2880_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_dec_ref(v___y_2885_);
lean_dec_ref(v___y_2880_);
return v___x_2887_;
}
else
{
lean_object* v_a_2888_; uint8_t v___x_2889_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
v___x_2889_ = l_Lean_Exception_isInterrupt(v_a_2888_);
if (v___x_2889_ == 0)
{
uint8_t v___x_2890_; 
lean_inc(v_a_2888_);
v___x_2890_ = l_Lean_Exception_isRuntime(v_a_2888_);
v___y_2860_ = v___y_2886_;
v___y_2861_ = v_a_2888_;
v___y_2862_ = v___y_2882_;
v___y_2863_ = v___x_2887_;
v___y_2864_ = v___y_2884_;
v___y_2865_ = v___y_2881_;
v___y_2866_ = v___y_2880_;
v___y_2867_ = v___y_2885_;
v___y_2868_ = v___y_2883_;
v___y_2869_ = v___x_2890_;
goto v___jp_2859_;
}
else
{
v___y_2860_ = v___y_2886_;
v___y_2861_ = v_a_2888_;
v___y_2862_ = v___y_2882_;
v___y_2863_ = v___x_2887_;
v___y_2864_ = v___y_2884_;
v___y_2865_ = v___y_2881_;
v___y_2866_ = v___y_2880_;
v___y_2867_ = v___y_2885_;
v___y_2868_ = v___y_2883_;
v___y_2869_ = v___x_2889_;
goto v___jp_2859_;
}
}
}
v___jp_2898_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Rewrite_3370143866____hygCtx___hyg_3_));
v___x_2906_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0(v___x_2905_, v___x_2897_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v___x_2907_; 
lean_dec_ref(v___x_2906_);
v___x_2907_ = l_Lean_Elab_Tactic_elabConfig(v_recover_2891_, v___x_2905_, v___x_2893_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2928_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2910_ = v___x_2907_;
v_isShared_2911_ = v_isSharedCheck_2928_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2928_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
uint8_t v___x_2912_; 
v___x_2912_ = l_Lean_Expr_hasSyntheticSorry(v_a_2908_);
if (v___x_2912_ == 0)
{
uint8_t v___x_2913_; 
lean_del_object(v___x_2910_);
v___x_2913_ = l_Lean_Expr_hasSorry(v_a_2908_);
if (v___x_2913_ == 0)
{
v___y_2880_ = v_a_2908_;
v___y_2881_ = v___y_2899_;
v___y_2882_ = v___y_2900_;
v___y_2883_ = v___y_2901_;
v___y_2884_ = v___y_2902_;
v___y_2885_ = v___y_2903_;
v___y_2886_ = v___y_2904_;
goto v___jp_2879_;
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_a_2908_);
v___x_2914_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__5, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__5);
v___x_2915_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(v___x_2914_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
lean_dec_ref(v___y_2903_);
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2915_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2915_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2926_; 
lean_dec(v_a_2908_);
lean_dec_ref(v___y_2903_);
v___x_2924_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__6));
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 0, v___x_2924_);
v___x_2926_ = v___x_2910_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec_ref(v___y_2903_);
v_a_2929_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2907_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2907_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref(v___y_2903_);
lean_dec_ref(v___x_2893_);
v_a_2937_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2906_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2906_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object* v_optConfig_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_optConfig_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec_ref(v_a_2980_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object* v_optConfig_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_optConfig_2989_, v_a_2990_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object* v_optConfig_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_Elab_Tactic_elabRewriteConfig(v_optConfig_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1(lean_object* v_00_u03b1_3011_, lean_object* v_msg_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___redArg(v_msg_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1___boxed(lean_object* v_00_u03b1_3021_, lean_object* v_msg_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1(v_00_u03b1_3021_, v_msg_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2(lean_object* v_00_u03b2_3031_, lean_object* v_m_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___redArg(v_m_3032_, v_a_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3035_, lean_object* v_m_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2(v_00_u03b2_3035_, v_m_3036_, v_a_3037_);
lean_dec(v_a_3037_);
lean_dec_ref(v_m_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4(lean_object* v_msgData_3039_, lean_object* v_macroStack_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___redArg(v_msgData_3039_, v_macroStack_3040_, v___y_3045_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4___boxed(lean_object* v_msgData_3049_, lean_object* v_macroStack_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__1_spec__4(v_msgData_3049_, v_macroStack_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
return v_res_3058_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3059_, lean_object* v_x_3060_, lean_object* v_x_3061_){
_start:
{
uint8_t v___x_3062_; 
v___x_3062_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___redArg(v_x_3060_, v_x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3063_, lean_object* v_x_3064_, lean_object* v_x_3065_){
_start:
{
uint8_t v_res_3066_; lean_object* v_r_3067_; 
v_res_3066_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1(v_00_u03b2_3063_, v_x_3064_, v_x_3065_);
lean_dec_ref(v_x_3065_);
lean_dec_ref(v_x_3064_);
v_r_3067_ = lean_box(v_res_3066_);
return v_r_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2(lean_object* v_cls_3068_, lean_object* v_msg_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___redArg(v_cls_3068_, v_msg_3069_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_3078_, lean_object* v_msg_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__2(v_cls_3078_, v_msg_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3088_, lean_object* v_a_3089_, lean_object* v_x_3090_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5___redArg(v_a_3089_, v_x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3092_, lean_object* v_a_3093_, lean_object* v_x_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__2_spec__5(v_00_u03b2_3092_, v_a_3093_, v_x_3094_);
lean_dec(v_x_3094_);
lean_dec(v_a_3093_);
return v_res_3095_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3096_, lean_object* v_x_3097_, size_t v_x_3098_, lean_object* v_x_3099_){
_start:
{
uint8_t v___x_3100_; 
v___x_3100_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3097_, v_x_3098_, v_x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3101_, lean_object* v_x_3102_, lean_object* v_x_3103_, lean_object* v_x_3104_){
_start:
{
size_t v_x_13024__boxed_3105_; uint8_t v_res_3106_; lean_object* v_r_3107_; 
v_x_13024__boxed_3105_ = lean_unbox_usize(v_x_3103_);
lean_dec(v_x_3103_);
v_res_3106_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3101_, v_x_3102_, v_x_13024__boxed_3105_, v_x_3104_);
lean_dec_ref(v_x_3104_);
lean_dec_ref(v_x_3102_);
v_r_3107_ = lean_box(v_res_3106_);
return v_r_3107_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_3108_, lean_object* v_keys_3109_, lean_object* v_vals_3110_, lean_object* v_heq_3111_, lean_object* v_i_3112_, lean_object* v_k_3113_){
_start:
{
uint8_t v___x_3114_; 
v___x_3114_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_keys_3109_, v_i_3112_, v_k_3113_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_3115_, lean_object* v_keys_3116_, lean_object* v_vals_3117_, lean_object* v_heq_3118_, lean_object* v_i_3119_, lean_object* v_k_3120_){
_start:
{
uint8_t v_res_3121_; lean_object* v_r_3122_; 
v_res_3121_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabRewriteConfig_spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_3115_, v_keys_3116_, v_vals_3117_, v_heq_3118_, v_i_3119_, v_k_3120_);
lean_dec_ref(v_k_3120_);
lean_dec_ref(v_vals_3117_);
lean_dec_ref(v_keys_3116_);
v_r_3122_ = lean_box(v_res_3121_);
return v_r_3122_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3));
v___x_3130_ = l_Lean_MessageData_ofFormat(v___x_3129_);
return v___x_3130_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4);
v___x_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object* v_x_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1));
v___x_3144_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5);
v___x_3145_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3143_, v_x_3133_, v___x_3144_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object* v_x_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(v_x_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object* v_term_3157_, uint8_t v_symm_3158_, lean_object* v_a_3159_, lean_object* v_x_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_term_3157_, v_symm_3158_, v_x_3160_, v_a_3159_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object* v_term_3171_, lean_object* v_symm_3172_, lean_object* v_a_3173_, lean_object* v_x_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
uint8_t v_symm_boxed_3184_; lean_object* v_res_3185_; 
v_symm_boxed_3184_ = lean_unbox(v_symm_3172_);
v_res_3185_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(v_term_3171_, v_symm_boxed_3184_, v_a_3173_, v_x_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object* v_a_3186_, lean_object* v___x_3187_, lean_object* v___f_3188_, uint8_t v_symm_3189_, lean_object* v_term_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; lean_object* v___f_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3200_ = lean_box(v_symm_3189_);
lean_inc_ref(v_a_3186_);
lean_inc(v_term_3190_);
v___f_3201_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed), 13, 3);
lean_closure_set(v___f_3201_, 0, v_term_3190_);
lean_closure_set(v___f_3201_, 1, v___x_3200_);
lean_closure_set(v___f_3201_, 2, v_a_3186_);
v___x_3202_ = lean_box(v_symm_3189_);
v___x_3203_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(v___x_3203_, 0, v_term_3190_);
lean_closure_set(v___x_3203_, 1, v___x_3202_);
lean_closure_set(v___x_3203_, 2, v_a_3186_);
v___x_3204_ = l_Lean_Elab_Tactic_withLocation(v___x_3187_, v___f_3201_, v___x_3203_, v___f_3188_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object* v_a_3205_, lean_object* v___x_3206_, lean_object* v___f_3207_, lean_object* v_symm_3208_, lean_object* v_term_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
uint8_t v_symm_boxed_3219_; lean_object* v_res_3220_; 
v_symm_boxed_3219_ = lean_unbox(v_symm_3208_);
v_res_3220_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(v_a_3205_, v___x_3206_, v___f_3207_, v_symm_boxed_3219_, v_term_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___x_3206_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object* v_stx_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_unsigned_to_nat(1u);
v___x_3233_ = l_Lean_Syntax_getArg(v_stx_3222_, v___x_3232_);
v___x_3234_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v___x_3233_, v_a_3223_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___f_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___f_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref(v___x_3234_);
v___f_3236_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__0));
v___x_3237_ = lean_unsigned_to_nat(3u);
v___x_3238_ = l_Lean_Syntax_getArg(v_stx_3222_, v___x_3237_);
v___x_3239_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_3238_);
lean_dec(v___x_3238_);
v___f_3240_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed), 14, 3);
lean_closure_set(v___f_3240_, 0, v_a_3235_);
lean_closure_set(v___f_3240_, 1, v___x_3239_);
lean_closure_set(v___f_3240_, 2, v___f_3236_);
v___x_3241_ = lean_unsigned_to_nat(0u);
v___x_3242_ = l_Lean_Syntax_getArg(v_stx_3222_, v___x_3241_);
v___x_3243_ = lean_unsigned_to_nat(2u);
v___x_3244_ = l_Lean_Syntax_getArg(v_stx_3222_, v___x_3243_);
v___x_3245_ = l_Lean_Elab_Tactic_withRWRulesSeq(v___x_3242_, v___x_3244_, v___f_3240_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
lean_dec(v___x_3244_);
return v___x_3245_;
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
v_a_3246_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3234_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3234_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object* v_stx_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Lean_Elab_Tactic_evalRewriteSeq(v_stx_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
lean_dec(v_a_3256_);
lean_dec_ref(v_a_3255_);
lean_dec(v_stx_3254_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3280_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3281_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2));
v___x_3282_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_3283_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___boxed), 10, 0);
v___x_3284_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3280_, v___x_3281_, v___x_3282_, v___x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3(){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6));
v___x_3315_ = l_Lean_addBuiltinDeclarationRanges(v___x_3313_, v___x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(lean_object* v_a_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
return v_res_3317_;
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
res = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
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
