// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Param
// Imports: public import Lean.Elab.Tactic.Grind.Basic import Lean.Meta.Tactic.Grind.ForallProp import Lean.Elab.Tactic.Grind.Anchor import Lean.Elab.SyntheticMVars
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Meta_Grind_CasesTypes_contains(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_isMatchEqLikeDeclName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_elabAnchorRef(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(lean_object*);
uint8_t l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremForDecl(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_backward_grind_inferPattern;
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_Grind_grindExt;
lean_object* l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_find___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_checkDeprecatedCore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SymbolPriorities_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_erase___redArg(lean_object*, lean_object*);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_assertExtra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_runParserCategory(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "this parameter is redundant, environment already contains `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` annotated with `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<input>"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unexpected modifier "};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "redundant modifier `!` in `grind` parameter"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "failed to generate equation theorems for `"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "invalid `grind` parameter, `"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "` is a definition, the only acceptable (and redundant) modifier is '='"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "` is a reducible definition, `grind` automatically unfolds them"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` is not a theorem, definition, or inductive type"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "invalid `grind` parameter, only global declarations are allowed when `+revert` is used"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 97, 194, 195, 68, 28, 219, 173)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "invalid `grind` parameter, failed to infer patterns"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "invalid `grind` parameter, parameter type is not a `forall` and is universe polymorphic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "invalid `grind` parameter, modifier is redundant since the parameter type is not a `forall`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid `grind` parameter, proof term expected"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "invalid `grind` parameter, only global declarations are allowed with this kind of modifier"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "invalid use of `usr` modifier, `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` does not have patterns specified with the command `grind_pattern`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`cases` parameter is not supported here"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "invalid use of `intro` modifier, `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`[grind ext]` cannot be set using parameters"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "normalization theorems should be registered using the `@[grind norm]` attribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "declarations to be unfolded during normalization should be registered using the `@[grind unfold]` attribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "homomorphism rules should be registered using the `@[grind hom]` attribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "homomorphism predicates should be registered using the `@[grind hom_pred]` attribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid use of modifier in `grind` attribute `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "redundant parameter `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "`, `grind` uses local hypotheses automatically"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindParam"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 144, 208, 205, 52, 106, 220, 83)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unexpected `grind` parameter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindErase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 172, 113, 174, 15, 5, 26, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindLemma"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(185, 180, 24, 243, 113, 54, 79, 133)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLemmaMin"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(65, 124, 255, 191, 121, 182, 88, 219)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "anchor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(168, 155, 228, 98, 168, 72, 115, 174)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "invalid anchor, `only` modifier expected"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "invalid `-` occurrence, it can only be used at the `grind` tactic entry point"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object**);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(lean_object* v_params_1_, lean_object* v_declName_2_, uint8_t v_eager_3_){
_start:
{
lean_object* v_config_4_; lean_object* v_extensions_5_; lean_object* v_extra_6_; lean_object* v_extraInj_7_; lean_object* v_extraFacts_8_; lean_object* v_symPrios_9_; lean_object* v_norm_10_; lean_object* v_normProcs_11_; lean_object* v_anchorRefs_x3f_12_; lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v_config_4_ = lean_ctor_get(v_params_1_, 0);
v_extensions_5_ = lean_ctor_get(v_params_1_, 1);
v_extra_6_ = lean_ctor_get(v_params_1_, 2);
v_extraInj_7_ = lean_ctor_get(v_params_1_, 3);
v_extraFacts_8_ = lean_ctor_get(v_params_1_, 4);
v_symPrios_9_ = lean_ctor_get(v_params_1_, 5);
v_norm_10_ = lean_ctor_get(v_params_1_, 6);
v_normProcs_11_ = lean_ctor_get(v_params_1_, 7);
v_anchorRefs_x3f_12_ = lean_ctor_get(v_params_1_, 8);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_array_get_size(v_extensions_5_);
v___x_15_ = lean_nat_dec_lt(v___x_13_, v___x_14_);
if (v___x_15_ == 0)
{
lean_dec(v_declName_2_);
return v_params_1_;
}
else
{
lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_39_; 
lean_inc(v_anchorRefs_x3f_12_);
lean_inc_ref(v_normProcs_11_);
lean_inc_ref(v_norm_10_);
lean_inc_ref(v_symPrios_9_);
lean_inc_ref(v_extraFacts_8_);
lean_inc_ref(v_extraInj_7_);
lean_inc_ref(v_extra_6_);
lean_inc_ref(v_extensions_5_);
lean_inc_ref(v_config_4_);
v_isSharedCheck_39_ = !lean_is_exclusive(v_params_1_);
if (v_isSharedCheck_39_ == 0)
{
lean_object* v_unused_40_; lean_object* v_unused_41_; lean_object* v_unused_42_; lean_object* v_unused_43_; lean_object* v_unused_44_; lean_object* v_unused_45_; lean_object* v_unused_46_; lean_object* v_unused_47_; lean_object* v_unused_48_; 
v_unused_40_ = lean_ctor_get(v_params_1_, 8);
lean_dec(v_unused_40_);
v_unused_41_ = lean_ctor_get(v_params_1_, 7);
lean_dec(v_unused_41_);
v_unused_42_ = lean_ctor_get(v_params_1_, 6);
lean_dec(v_unused_42_);
v_unused_43_ = lean_ctor_get(v_params_1_, 5);
lean_dec(v_unused_43_);
v_unused_44_ = lean_ctor_get(v_params_1_, 4);
lean_dec(v_unused_44_);
v_unused_45_ = lean_ctor_get(v_params_1_, 3);
lean_dec(v_unused_45_);
v_unused_46_ = lean_ctor_get(v_params_1_, 2);
lean_dec(v_unused_46_);
v_unused_47_ = lean_ctor_get(v_params_1_, 1);
lean_dec(v_unused_47_);
v_unused_48_ = lean_ctor_get(v_params_1_, 0);
lean_dec(v_unused_48_);
v___x_17_ = v_params_1_;
v_isShared_18_ = v_isSharedCheck_39_;
goto v_resetjp_16_;
}
else
{
lean_dec(v_params_1_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_39_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v_v_19_; lean_object* v_casesTypes_20_; lean_object* v_extThms_21_; lean_object* v_funCC_22_; lean_object* v_ematch_23_; lean_object* v_inj_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_38_; 
v_v_19_ = lean_array_fget(v_extensions_5_, v___x_13_);
v_casesTypes_20_ = lean_ctor_get(v_v_19_, 0);
v_extThms_21_ = lean_ctor_get(v_v_19_, 1);
v_funCC_22_ = lean_ctor_get(v_v_19_, 2);
v_ematch_23_ = lean_ctor_get(v_v_19_, 3);
v_inj_24_ = lean_ctor_get(v_v_19_, 4);
v_isSharedCheck_38_ = !lean_is_exclusive(v_v_19_);
if (v_isSharedCheck_38_ == 0)
{
v___x_26_ = v_v_19_;
v_isShared_27_ = v_isSharedCheck_38_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_inj_24_);
lean_inc(v_ematch_23_);
lean_inc(v_funCC_22_);
lean_inc(v_extThms_21_);
lean_inc(v_casesTypes_20_);
lean_dec(v_v_19_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_38_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v_xs_x27_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_28_ = lean_box(0);
v_xs_x27_29_ = lean_array_fset(v_extensions_5_, v___x_13_, v___x_28_);
v___x_30_ = l_Lean_Meta_Grind_CasesTypes_insert(v_casesTypes_20_, v_declName_2_, v_eager_3_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_30_);
v___x_32_ = v___x_26_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_extThms_21_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v_funCC_22_);
lean_ctor_set(v_reuseFailAlloc_37_, 3, v_ematch_23_);
lean_ctor_set(v_reuseFailAlloc_37_, 4, v_inj_24_);
v___x_32_ = v_reuseFailAlloc_37_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = lean_array_fset(v_xs_x27_29_, v___x_13_, v___x_32_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___x_33_);
v___x_35_ = v___x_17_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_config_4_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_36_, 2, v_extra_6_);
lean_ctor_set(v_reuseFailAlloc_36_, 3, v_extraInj_7_);
lean_ctor_set(v_reuseFailAlloc_36_, 4, v_extraFacts_8_);
lean_ctor_set(v_reuseFailAlloc_36_, 5, v_symPrios_9_);
lean_ctor_set(v_reuseFailAlloc_36_, 6, v_norm_10_);
lean_ctor_set(v_reuseFailAlloc_36_, 7, v_normProcs_11_);
lean_ctor_set(v_reuseFailAlloc_36_, 8, v_anchorRefs_x3f_12_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes___boxed(lean_object* v_params_49_, lean_object* v_declName_50_, lean_object* v_eager_51_){
_start:
{
uint8_t v_eager_boxed_52_; lean_object* v_res_53_; 
v_eager_boxed_52_ = lean_unbox(v_eager_51_);
v_res_53_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_49_, v_declName_50_, v_eager_boxed_52_);
return v_res_53_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(lean_object* v_declName_54_, lean_object* v_as_55_, size_t v_i_56_, size_t v_stop_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = lean_usize_dec_eq(v_i_56_, v_stop_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v_casesTypes_60_; uint8_t v___x_61_; 
v___x_59_ = lean_array_uget_borrowed(v_as_55_, v_i_56_);
v_casesTypes_60_ = lean_ctor_get(v___x_59_, 0);
v___x_61_ = l_Lean_Meta_Grind_CasesTypes_contains(v_casesTypes_60_, v_declName_54_);
if (v___x_61_ == 0)
{
size_t v___x_62_; size_t v___x_63_; 
v___x_62_ = ((size_t)1ULL);
v___x_63_ = lean_usize_add(v_i_56_, v___x_62_);
v_i_56_ = v___x_63_;
goto _start;
}
else
{
return v___x_61_;
}
}
else
{
uint8_t v___x_65_; 
v___x_65_ = 0;
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0___boxed(lean_object* v_declName_66_, lean_object* v_as_67_, lean_object* v_i_68_, lean_object* v_stop_69_){
_start:
{
size_t v_i_boxed_70_; size_t v_stop_boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_i_boxed_70_ = lean_unbox_usize(v_i_68_);
lean_dec(v_i_68_);
v_stop_boxed_71_ = lean_unbox_usize(v_stop_69_);
lean_dec(v_stop_69_);
v_res_72_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(v_declName_66_, v_as_67_, v_i_boxed_70_, v_stop_boxed_71_);
lean_dec_ref(v_as_67_);
lean_dec(v_declName_66_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(lean_object* v_params_74_, lean_object* v_declName_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___y_83_; lean_object* v___y_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v_config_91_; lean_object* v_extensions_92_; lean_object* v_extra_93_; lean_object* v_extraInj_94_; lean_object* v_extraFacts_95_; lean_object* v_symPrios_96_; lean_object* v_norm_97_; lean_object* v_normProcs_98_; lean_object* v_anchorRefs_x3f_99_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_config_91_ = lean_ctor_get(v_params_74_, 0);
lean_inc_ref(v_config_91_);
v_extensions_92_ = lean_ctor_get(v_params_74_, 1);
lean_inc_ref(v_extensions_92_);
v_extra_93_ = lean_ctor_get(v_params_74_, 2);
lean_inc_ref(v_extra_93_);
v_extraInj_94_ = lean_ctor_get(v_params_74_, 3);
lean_inc_ref(v_extraInj_94_);
v_extraFacts_95_ = lean_ctor_get(v_params_74_, 4);
lean_inc_ref(v_extraFacts_95_);
v_symPrios_96_ = lean_ctor_get(v_params_74_, 5);
lean_inc_ref(v_symPrios_96_);
v_norm_97_ = lean_ctor_get(v_params_74_, 6);
lean_inc_ref(v_norm_97_);
v_normProcs_98_ = lean_ctor_get(v_params_74_, 7);
lean_inc_ref(v_normProcs_98_);
v_anchorRefs_x3f_99_ = lean_ctor_get(v_params_74_, 8);
lean_inc(v_anchorRefs_x3f_99_);
lean_dec_ref(v_params_74_);
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_array_get_size(v_extensions_92_);
v___x_133_ = lean_nat_dec_lt(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
goto v___jp_121_;
}
else
{
if (v___x_133_ == 0)
{
goto v___jp_121_;
}
else
{
size_t v___x_134_; size_t v___x_135_; uint8_t v___x_136_; 
v___x_134_ = ((size_t)0ULL);
v___x_135_ = lean_usize_of_nat(v___x_132_);
v___x_136_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(v_declName_75_, v_extensions_92_, v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
goto v___jp_121_;
}
else
{
goto v___jp_100_;
}
}
}
v___jp_79_:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_89_, 0, v___y_87_);
lean_ctor_set(v___x_89_, 1, v___y_88_);
lean_ctor_set(v___x_89_, 2, v___y_82_);
lean_ctor_set(v___x_89_, 3, v___y_86_);
lean_ctor_set(v___x_89_, 4, v___y_84_);
lean_ctor_set(v___x_89_, 5, v___y_83_);
lean_ctor_set(v___x_89_, 6, v___y_85_);
lean_ctor_set(v___x_89_, 7, v___y_80_);
lean_ctor_set(v___x_89_, 8, v___y_81_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
v___jp_100_:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_array_get_size(v_extensions_92_);
v___x_103_ = lean_nat_dec_lt(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_dec(v_declName_75_);
v___y_80_ = v_normProcs_98_;
v___y_81_ = v_anchorRefs_x3f_99_;
v___y_82_ = v_extra_93_;
v___y_83_ = v_symPrios_96_;
v___y_84_ = v_extraFacts_95_;
v___y_85_ = v_norm_97_;
v___y_86_ = v_extraInj_94_;
v___y_87_ = v_config_91_;
v___y_88_ = v_extensions_92_;
goto v___jp_79_;
}
else
{
lean_object* v_v_104_; lean_object* v_casesTypes_105_; lean_object* v_extThms_106_; lean_object* v_funCC_107_; lean_object* v_ematch_108_; lean_object* v_inj_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_120_; 
v_v_104_ = lean_array_fget(v_extensions_92_, v___x_101_);
v_casesTypes_105_ = lean_ctor_get(v_v_104_, 0);
v_extThms_106_ = lean_ctor_get(v_v_104_, 1);
v_funCC_107_ = lean_ctor_get(v_v_104_, 2);
v_ematch_108_ = lean_ctor_get(v_v_104_, 3);
v_inj_109_ = lean_ctor_get(v_v_104_, 4);
v_isSharedCheck_120_ = !lean_is_exclusive(v_v_104_);
if (v_isSharedCheck_120_ == 0)
{
v___x_111_ = v_v_104_;
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_inj_109_);
lean_inc(v_ematch_108_);
lean_inc(v_funCC_107_);
lean_inc(v_extThms_106_);
lean_inc(v_casesTypes_105_);
lean_dec(v_v_104_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v_xs_x27_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_113_ = lean_box(0);
v_xs_x27_114_ = lean_array_fset(v_extensions_92_, v___x_101_, v___x_113_);
v___x_115_ = l_Lean_Meta_Grind_CasesTypes_erase(v_casesTypes_105_, v_declName_75_);
lean_dec(v_declName_75_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_115_);
v___x_117_ = v___x_111_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_extThms_106_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_funCC_107_);
lean_ctor_set(v_reuseFailAlloc_119_, 3, v_ematch_108_);
lean_ctor_set(v_reuseFailAlloc_119_, 4, v_inj_109_);
v___x_117_ = v_reuseFailAlloc_119_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; 
v___x_118_ = lean_array_fset(v_xs_x27_114_, v___x_101_, v___x_117_);
v___y_80_ = v_normProcs_98_;
v___y_81_ = v_anchorRefs_x3f_99_;
v___y_82_ = v_extra_93_;
v___y_83_ = v_symPrios_96_;
v___y_84_ = v_extraFacts_95_;
v___y_85_ = v_norm_97_;
v___y_86_ = v_extraInj_94_;
v___y_87_ = v_config_91_;
v___y_88_ = v___x_118_;
goto v___jp_79_;
}
}
}
}
v___jp_121_:
{
lean_object* v___x_122_; 
lean_inc(v_declName_75_);
v___x_122_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_dec_ref_known(v___x_122_, 1);
goto v___jp_100_;
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_anchorRefs_x3f_99_);
lean_dec_ref(v_normProcs_98_);
lean_dec_ref(v_norm_97_);
lean_dec_ref(v_symPrios_96_);
lean_dec_ref(v_extraFacts_95_);
lean_dec_ref(v_extraInj_94_);
lean_dec_ref(v_extra_93_);
lean_dec_ref(v_extensions_92_);
lean_dec_ref(v_config_91_);
lean_dec(v_declName_75_);
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes___boxed(lean_object* v_params_137_, lean_object* v_declName_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_params_137_, v_declName_138_, v_a_139_, v_a_140_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(lean_object* v_params_143_, lean_object* v_declName_144_){
_start:
{
lean_object* v_config_145_; lean_object* v_extensions_146_; lean_object* v_extra_147_; lean_object* v_extraInj_148_; lean_object* v_extraFacts_149_; lean_object* v_symPrios_150_; lean_object* v_norm_151_; lean_object* v_normProcs_152_; lean_object* v_anchorRefs_x3f_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v_config_145_ = lean_ctor_get(v_params_143_, 0);
v_extensions_146_ = lean_ctor_get(v_params_143_, 1);
v_extra_147_ = lean_ctor_get(v_params_143_, 2);
v_extraInj_148_ = lean_ctor_get(v_params_143_, 3);
v_extraFacts_149_ = lean_ctor_get(v_params_143_, 4);
v_symPrios_150_ = lean_ctor_get(v_params_143_, 5);
v_norm_151_ = lean_ctor_get(v_params_143_, 6);
v_normProcs_152_ = lean_ctor_get(v_params_143_, 7);
v_anchorRefs_x3f_153_ = lean_ctor_get(v_params_143_, 8);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_array_get_size(v_extensions_146_);
v___x_156_ = lean_nat_dec_lt(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_dec(v_declName_144_);
return v_params_143_;
}
else
{
lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_180_; 
lean_inc(v_anchorRefs_x3f_153_);
lean_inc_ref(v_normProcs_152_);
lean_inc_ref(v_norm_151_);
lean_inc_ref(v_symPrios_150_);
lean_inc_ref(v_extraFacts_149_);
lean_inc_ref(v_extraInj_148_);
lean_inc_ref(v_extra_147_);
lean_inc_ref(v_extensions_146_);
lean_inc_ref(v_config_145_);
v_isSharedCheck_180_ = !lean_is_exclusive(v_params_143_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; lean_object* v_unused_182_; lean_object* v_unused_183_; lean_object* v_unused_184_; lean_object* v_unused_185_; lean_object* v_unused_186_; lean_object* v_unused_187_; lean_object* v_unused_188_; lean_object* v_unused_189_; 
v_unused_181_ = lean_ctor_get(v_params_143_, 8);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_params_143_, 7);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_params_143_, 6);
lean_dec(v_unused_183_);
v_unused_184_ = lean_ctor_get(v_params_143_, 5);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_params_143_, 4);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_params_143_, 3);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_params_143_, 2);
lean_dec(v_unused_187_);
v_unused_188_ = lean_ctor_get(v_params_143_, 1);
lean_dec(v_unused_188_);
v_unused_189_ = lean_ctor_get(v_params_143_, 0);
lean_dec(v_unused_189_);
v___x_158_ = v_params_143_;
v_isShared_159_ = v_isSharedCheck_180_;
goto v_resetjp_157_;
}
else
{
lean_dec(v_params_143_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_180_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_v_160_; lean_object* v_casesTypes_161_; lean_object* v_extThms_162_; lean_object* v_funCC_163_; lean_object* v_ematch_164_; lean_object* v_inj_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_179_; 
v_v_160_ = lean_array_fget(v_extensions_146_, v___x_154_);
v_casesTypes_161_ = lean_ctor_get(v_v_160_, 0);
v_extThms_162_ = lean_ctor_get(v_v_160_, 1);
v_funCC_163_ = lean_ctor_get(v_v_160_, 2);
v_ematch_164_ = lean_ctor_get(v_v_160_, 3);
v_inj_165_ = lean_ctor_get(v_v_160_, 4);
v_isSharedCheck_179_ = !lean_is_exclusive(v_v_160_);
if (v_isSharedCheck_179_ == 0)
{
v___x_167_ = v_v_160_;
v_isShared_168_ = v_isSharedCheck_179_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_inj_165_);
lean_inc(v_ematch_164_);
lean_inc(v_funCC_163_);
lean_inc(v_extThms_162_);
lean_inc(v_casesTypes_161_);
lean_dec(v_v_160_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_179_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v_xs_x27_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_169_ = lean_box(0);
v_xs_x27_170_ = lean_array_fset(v_extensions_146_, v___x_154_, v___x_169_);
v___x_171_ = l_Lean_NameSet_insert(v_funCC_163_, v_declName_144_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 2, v___x_171_);
v___x_173_ = v___x_167_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_casesTypes_161_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_extThms_162_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_178_, 3, v_ematch_164_);
lean_ctor_set(v_reuseFailAlloc_178_, 4, v_inj_165_);
v___x_173_ = v_reuseFailAlloc_178_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_array_fset(v_xs_x27_170_, v___x_154_, v___x_173_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_174_);
v___x_176_ = v___x_158_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_config_145_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_extra_147_);
lean_ctor_set(v_reuseFailAlloc_177_, 3, v_extraInj_148_);
lean_ctor_set(v_reuseFailAlloc_177_, 4, v_extraFacts_149_);
lean_ctor_set(v_reuseFailAlloc_177_, 5, v_symPrios_150_);
lean_ctor_set(v_reuseFailAlloc_177_, 6, v_norm_151_);
lean_ctor_set(v_reuseFailAlloc_177_, 7, v_normProcs_152_);
lean_ctor_set(v_reuseFailAlloc_177_, 8, v_anchorRefs_x3f_153_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(lean_object* v_declName_190_, lean_object* v_as_191_, size_t v_i_192_, size_t v_stop_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_eq(v_i_192_, v_stop_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v_ematch_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_195_ = lean_array_uget_borrowed(v_as_191_, v_i_192_);
v_ematch_196_ = lean_ctor_get(v___x_195_, 3);
lean_inc(v_declName_190_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v_declName_190_);
v___x_198_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_ematch_196_, v___x_197_);
lean_dec_ref_known(v___x_197_, 1);
if (v___x_198_ == 0)
{
size_t v___x_199_; size_t v___x_200_; 
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_add(v_i_192_, v___x_199_);
v_i_192_ = v___x_200_;
goto _start;
}
else
{
lean_dec(v_declName_190_);
return v___x_198_;
}
}
else
{
uint8_t v___x_202_; 
lean_dec(v_declName_190_);
v___x_202_ = 0;
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0___boxed(lean_object* v_declName_203_, lean_object* v_as_204_, lean_object* v_i_205_, lean_object* v_stop_206_){
_start:
{
size_t v_i_boxed_207_; size_t v_stop_boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_i_boxed_207_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_stop_boxed_208_ = lean_unbox_usize(v_stop_206_);
lean_dec(v_stop_206_);
v_res_209_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(v_declName_203_, v_as_204_, v_i_boxed_207_, v_stop_boxed_208_);
lean_dec_ref(v_as_204_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(lean_object* v_params_211_, lean_object* v_declName_212_){
_start:
{
lean_object* v_extensions_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_extensions_213_ = lean_ctor_get(v_params_211_, 1);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_array_get_size(v_extensions_213_);
v___x_216_ = lean_nat_dec_lt(v___x_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec(v_declName_212_);
return v___x_216_;
}
else
{
if (v___x_216_ == 0)
{
lean_dec(v_declName_212_);
return v___x_216_;
}
else
{
size_t v___x_217_; size_t v___x_218_; uint8_t v___x_219_; 
v___x_217_ = ((size_t)0ULL);
v___x_218_ = lean_usize_of_nat(v___x_215_);
v___x_219_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(v_declName_212_, v_extensions_213_, v___x_217_, v___x_218_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch___boxed(lean_object* v_params_220_, lean_object* v_declName_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_220_, v_declName_221_);
lean_dec_ref(v_params_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(lean_object* v_declName_224_, lean_object* v_as_225_, size_t v_i_226_, size_t v_stop_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_eq(v_i_226_, v_stop_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v_inj_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_229_ = lean_array_uget_borrowed(v_as_225_, v_i_226_);
v_inj_230_ = lean_ctor_get(v___x_229_, 4);
lean_inc(v_declName_224_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v_declName_224_);
v___x_232_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_230_, v___x_231_);
lean_dec_ref_known(v___x_231_, 1);
if (v___x_232_ == 0)
{
size_t v___x_233_; size_t v___x_234_; 
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_add(v_i_226_, v___x_233_);
v_i_226_ = v___x_234_;
goto _start;
}
else
{
lean_dec(v_declName_224_);
return v___x_232_;
}
}
else
{
uint8_t v___x_236_; 
lean_dec(v_declName_224_);
v___x_236_ = 0;
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0___boxed(lean_object* v_declName_237_, lean_object* v_as_238_, lean_object* v_i_239_, lean_object* v_stop_240_){
_start:
{
size_t v_i_boxed_241_; size_t v_stop_boxed_242_; uint8_t v_res_243_; lean_object* v_r_244_; 
v_i_boxed_241_ = lean_unbox_usize(v_i_239_);
lean_dec(v_i_239_);
v_stop_boxed_242_ = lean_unbox_usize(v_stop_240_);
lean_dec(v_stop_240_);
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(v_declName_237_, v_as_238_, v_i_boxed_241_, v_stop_boxed_242_);
lean_dec_ref(v_as_238_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(lean_object* v_params_245_, lean_object* v_declName_246_){
_start:
{
lean_object* v_extensions_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v_extensions_247_ = lean_ctor_get(v_params_245_, 1);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_array_get_size(v_extensions_247_);
v___x_250_ = lean_nat_dec_lt(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
lean_dec(v_declName_246_);
return v___x_250_;
}
else
{
if (v___x_250_ == 0)
{
lean_dec(v_declName_246_);
return v___x_250_;
}
else
{
size_t v___x_251_; size_t v___x_252_; uint8_t v___x_253_; 
v___x_251_ = ((size_t)0ULL);
v___x_252_ = lean_usize_of_nat(v___x_249_);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(v_declName_246_, v_extensions_247_, v___x_251_, v___x_252_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem___boxed(lean_object* v_params_254_, lean_object* v_declName_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_params_254_, v_declName_255_);
lean_dec_ref(v_params_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(lean_object* v_params_258_, lean_object* v_declName_259_){
_start:
{
lean_object* v_config_260_; lean_object* v_extensions_261_; lean_object* v_extra_262_; lean_object* v_extraInj_263_; lean_object* v_extraFacts_264_; lean_object* v_symPrios_265_; lean_object* v_norm_266_; lean_object* v_normProcs_267_; lean_object* v_anchorRefs_x3f_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_config_260_ = lean_ctor_get(v_params_258_, 0);
v_extensions_261_ = lean_ctor_get(v_params_258_, 1);
v_extra_262_ = lean_ctor_get(v_params_258_, 2);
v_extraInj_263_ = lean_ctor_get(v_params_258_, 3);
v_extraFacts_264_ = lean_ctor_get(v_params_258_, 4);
v_symPrios_265_ = lean_ctor_get(v_params_258_, 5);
v_norm_266_ = lean_ctor_get(v_params_258_, 6);
v_normProcs_267_ = lean_ctor_get(v_params_258_, 7);
v_anchorRefs_x3f_268_ = lean_ctor_get(v_params_258_, 8);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_array_get_size(v_extensions_261_);
v___x_271_ = lean_nat_dec_lt(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec(v_declName_259_);
return v_params_258_;
}
else
{
lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_296_; 
lean_inc(v_anchorRefs_x3f_268_);
lean_inc_ref(v_normProcs_267_);
lean_inc_ref(v_norm_266_);
lean_inc_ref(v_symPrios_265_);
lean_inc_ref(v_extraFacts_264_);
lean_inc_ref(v_extraInj_263_);
lean_inc_ref(v_extra_262_);
lean_inc_ref(v_extensions_261_);
lean_inc_ref(v_config_260_);
v_isSharedCheck_296_ = !lean_is_exclusive(v_params_258_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; lean_object* v_unused_300_; lean_object* v_unused_301_; lean_object* v_unused_302_; lean_object* v_unused_303_; lean_object* v_unused_304_; lean_object* v_unused_305_; 
v_unused_297_ = lean_ctor_get(v_params_258_, 8);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_params_258_, 7);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_params_258_, 6);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_params_258_, 5);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_params_258_, 4);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_params_258_, 3);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_params_258_, 2);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_params_258_, 1);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_params_258_, 0);
lean_dec(v_unused_305_);
v___x_273_ = v_params_258_;
v_isShared_274_ = v_isSharedCheck_296_;
goto v_resetjp_272_;
}
else
{
lean_dec(v_params_258_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_296_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_v_275_; lean_object* v_casesTypes_276_; lean_object* v_extThms_277_; lean_object* v_funCC_278_; lean_object* v_ematch_279_; lean_object* v_inj_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_295_; 
v_v_275_ = lean_array_fget(v_extensions_261_, v___x_269_);
v_casesTypes_276_ = lean_ctor_get(v_v_275_, 0);
v_extThms_277_ = lean_ctor_get(v_v_275_, 1);
v_funCC_278_ = lean_ctor_get(v_v_275_, 2);
v_ematch_279_ = lean_ctor_get(v_v_275_, 3);
v_inj_280_ = lean_ctor_get(v_v_275_, 4);
v_isSharedCheck_295_ = !lean_is_exclusive(v_v_275_);
if (v_isSharedCheck_295_ == 0)
{
v___x_282_ = v_v_275_;
v_isShared_283_ = v_isSharedCheck_295_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_inj_280_);
lean_inc(v_ematch_279_);
lean_inc(v_funCC_278_);
lean_inc(v_extThms_277_);
lean_inc(v_casesTypes_276_);
lean_dec(v_v_275_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_295_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v_xs_x27_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_284_ = lean_box(0);
v_xs_x27_285_ = lean_array_fset(v_extensions_261_, v___x_269_, v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_declName_259_);
v___x_287_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_ematch_279_, v___x_286_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 3, v___x_287_);
v___x_289_ = v___x_282_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_casesTypes_276_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_extThms_277_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_funCC_278_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_294_, 4, v_inj_280_);
v___x_289_ = v_reuseFailAlloc_294_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_array_fset(v_xs_x27_285_, v___x_269_, v___x_289_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v___x_290_);
v___x_292_ = v___x_273_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_config_260_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_extra_262_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_extraInj_263_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v_extraFacts_264_);
lean_ctor_set(v_reuseFailAlloc_293_, 5, v_symPrios_265_);
lean_ctor_set(v_reuseFailAlloc_293_, 6, v_norm_266_);
lean_ctor_set(v_reuseFailAlloc_293_, 7, v_normProcs_267_);
lean_ctor_set(v_reuseFailAlloc_293_, 8, v_anchorRefs_x3f_268_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object* v_params_306_, uint8_t v___x_307_, lean_object* v_as_308_, size_t v_i_309_, size_t v_stop_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_eq(v_i_309_, v_stop_310_);
if (v___x_311_ == 0)
{
uint8_t v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_312_ = 1;
v___x_313_ = lean_array_uget_borrowed(v_as_308_, v_i_309_);
lean_inc(v___x_313_);
v___x_314_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_306_, v___x_313_);
if (v___x_314_ == 0)
{
return v___x_312_;
}
else
{
if (v___x_307_ == 0)
{
size_t v___x_315_; size_t v___x_316_; 
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_add(v_i_309_, v___x_315_);
v_i_309_ = v___x_316_;
goto _start;
}
else
{
return v___x_312_;
}
}
}
else
{
uint8_t v___x_318_; 
v___x_318_ = 0;
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object* v_params_319_, lean_object* v___x_320_, lean_object* v_as_321_, lean_object* v_i_322_, lean_object* v_stop_323_){
_start:
{
uint8_t v___x_1646__boxed_324_; size_t v_i_boxed_325_; size_t v_stop_boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v___x_1646__boxed_324_ = lean_unbox(v___x_320_);
v_i_boxed_325_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_stop_boxed_326_ = lean_unbox_usize(v_stop_323_);
lean_dec(v_stop_323_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_319_, v___x_1646__boxed_324_, v_as_321_, v_i_boxed_325_, v_stop_boxed_326_);
lean_dec_ref(v_as_321_);
lean_dec_ref(v_params_319_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_, lean_object* v_b_332_){
_start:
{
uint8_t v___x_333_; 
v___x_333_ = lean_usize_dec_eq(v_i_330_, v_stop_331_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; size_t v___x_336_; size_t v___x_337_; 
v___x_334_ = lean_array_uget_borrowed(v_as_329_, v_i_330_);
lean_inc(v___x_334_);
v___x_335_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(v_b_332_, v___x_334_);
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_330_, v___x_336_);
v_i_330_ = v___x_337_;
v_b_332_ = v___x_335_;
goto _start;
}
else
{
return v_b_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0___boxed(lean_object* v_as_339_, lean_object* v_i_340_, lean_object* v_stop_341_, lean_object* v_b_342_){
_start:
{
size_t v_i_boxed_343_; size_t v_stop_boxed_344_; lean_object* v_res_345_; 
v_i_boxed_343_ = lean_unbox_usize(v_i_340_);
lean_dec(v_i_340_);
v_stop_boxed_344_ = lean_unbox_usize(v_stop_341_);
lean_dec(v_stop_341_);
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_as_339_, v_i_boxed_343_, v_stop_boxed_344_, v_b_342_);
lean_dec_ref(v_as_339_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(lean_object* v_params_346_, lean_object* v_declName_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_356_; lean_object* v_env_357_; uint8_t v___x_358_; 
v___x_356_ = lean_st_ref_get(v_a_351_);
v_env_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc_ref(v_env_357_);
lean_dec(v___x_356_);
lean_inc(v_declName_347_);
v___x_358_ = l_Lean_wasOriginallyTheorem(v_env_357_, v_declName_347_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
lean_inc(v_declName_347_);
v___x_359_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_404_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_404_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_404_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_404_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
if (lean_obj_tag(v_a_360_) == 1)
{
lean_object* v_val_364_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_val_364_ = lean_ctor_get(v_a_360_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v_a_360_, 1);
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = lean_array_get_size(v_val_364_);
v___x_390_ = lean_nat_dec_lt(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_dec(v_declName_347_);
goto v___jp_365_;
}
else
{
if (v___x_390_ == 0)
{
lean_dec(v_declName_347_);
goto v___jp_365_;
}
else
{
size_t v___x_391_; size_t v___x_392_; uint8_t v___x_393_; 
v___x_391_ = ((size_t)0ULL);
v___x_392_ = lean_usize_of_nat(v___x_389_);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_346_, v___x_358_, v_val_364_, v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_dec(v_declName_347_);
goto v___jp_365_;
}
else
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_347_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_dec_ref_known(v___x_394_, 1);
goto v___jp_365_;
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_val_364_);
lean_del_object(v___x_362_);
lean_dec_ref(v_params_346_);
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
v___jp_365_:
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_array_get_size(v_val_364_);
v___x_368_ = lean_nat_dec_lt(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_370_; 
lean_dec(v_val_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v_params_346_);
v___x_370_ = v___x_362_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_params_346_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
else
{
uint8_t v___x_372_; 
v___x_372_ = lean_nat_dec_le(v___x_367_, v___x_367_);
if (v___x_372_ == 0)
{
if (v___x_368_ == 0)
{
lean_object* v___x_374_; 
lean_dec(v_val_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v_params_346_);
v___x_374_ = v___x_362_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_params_346_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_376_ = ((size_t)0ULL);
v___x_377_ = lean_usize_of_nat(v___x_367_);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_364_, v___x_376_, v___x_377_, v_params_346_);
lean_dec(v_val_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_378_);
v___x_380_ = v___x_362_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_382_ = ((size_t)0ULL);
v___x_383_ = lean_usize_of_nat(v___x_367_);
v___x_384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_364_, v___x_382_, v___x_383_, v_params_346_);
lean_dec(v_val_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_384_);
v___x_386_ = v___x_362_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
else
{
lean_object* v___x_403_; 
lean_del_object(v___x_362_);
lean_dec(v_a_360_);
lean_dec_ref(v_params_346_);
v___x_403_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_347_, v_a_350_, v_a_351_);
return v___x_403_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_declName_347_);
lean_dec_ref(v_params_346_);
v_a_405_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_359_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_359_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
uint8_t v___x_413_; 
lean_inc(v_declName_347_);
v___x_413_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_346_, v_declName_347_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
lean_inc(v_declName_347_);
v___x_414_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_347_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_dec_ref_known(v___x_414_, 1);
goto v___jp_353_;
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec(v_declName_347_);
lean_dec_ref(v_params_346_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
goto v___jp_353_;
}
}
v___jp_353_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(v_params_346_, v_declName_347_);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch___boxed(lean_object* v_params_423_, lean_object* v_declName_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_params_423_, v_declName_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(lean_object* v_params_431_, lean_object* v_declName_432_){
_start:
{
lean_object* v_config_433_; lean_object* v_extensions_434_; lean_object* v_extra_435_; lean_object* v_extraInj_436_; lean_object* v_extraFacts_437_; lean_object* v_symPrios_438_; lean_object* v_norm_439_; lean_object* v_normProcs_440_; lean_object* v_anchorRefs_x3f_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_config_433_ = lean_ctor_get(v_params_431_, 0);
v_extensions_434_ = lean_ctor_get(v_params_431_, 1);
v_extra_435_ = lean_ctor_get(v_params_431_, 2);
v_extraInj_436_ = lean_ctor_get(v_params_431_, 3);
v_extraFacts_437_ = lean_ctor_get(v_params_431_, 4);
v_symPrios_438_ = lean_ctor_get(v_params_431_, 5);
v_norm_439_ = lean_ctor_get(v_params_431_, 6);
v_normProcs_440_ = lean_ctor_get(v_params_431_, 7);
v_anchorRefs_x3f_441_ = lean_ctor_get(v_params_431_, 8);
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_array_get_size(v_extensions_434_);
v___x_444_ = lean_nat_dec_lt(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_dec(v_declName_432_);
return v_params_431_;
}
else
{
lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_469_; 
lean_inc(v_anchorRefs_x3f_441_);
lean_inc_ref(v_normProcs_440_);
lean_inc_ref(v_norm_439_);
lean_inc_ref(v_symPrios_438_);
lean_inc_ref(v_extraFacts_437_);
lean_inc_ref(v_extraInj_436_);
lean_inc_ref(v_extra_435_);
lean_inc_ref(v_extensions_434_);
lean_inc_ref(v_config_433_);
v_isSharedCheck_469_ = !lean_is_exclusive(v_params_431_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_470_ = lean_ctor_get(v_params_431_, 8);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_params_431_, 7);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_params_431_, 6);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_params_431_, 5);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_params_431_, 4);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_params_431_, 3);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_params_431_, 2);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_params_431_, 1);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_params_431_, 0);
lean_dec(v_unused_478_);
v___x_446_ = v_params_431_;
v_isShared_447_ = v_isSharedCheck_469_;
goto v_resetjp_445_;
}
else
{
lean_dec(v_params_431_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_469_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_v_448_; lean_object* v_casesTypes_449_; lean_object* v_extThms_450_; lean_object* v_funCC_451_; lean_object* v_ematch_452_; lean_object* v_inj_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_468_; 
v_v_448_ = lean_array_fget(v_extensions_434_, v___x_442_);
v_casesTypes_449_ = lean_ctor_get(v_v_448_, 0);
v_extThms_450_ = lean_ctor_get(v_v_448_, 1);
v_funCC_451_ = lean_ctor_get(v_v_448_, 2);
v_ematch_452_ = lean_ctor_get(v_v_448_, 3);
v_inj_453_ = lean_ctor_get(v_v_448_, 4);
v_isSharedCheck_468_ = !lean_is_exclusive(v_v_448_);
if (v_isSharedCheck_468_ == 0)
{
v___x_455_ = v_v_448_;
v_isShared_456_ = v_isSharedCheck_468_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_inj_453_);
lean_inc(v_ematch_452_);
lean_inc(v_funCC_451_);
lean_inc(v_extThms_450_);
lean_inc(v_casesTypes_449_);
lean_dec(v_v_448_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_468_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v_xs_x27_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_457_ = lean_box(0);
v_xs_x27_458_ = lean_array_fset(v_extensions_434_, v___x_442_, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_declName_432_);
v___x_460_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_inj_453_, v___x_459_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_460_);
v___x_462_ = v___x_455_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_casesTypes_449_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_extThms_450_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_funCC_451_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v_ematch_452_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v___x_460_);
v___x_462_ = v_reuseFailAlloc_467_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_array_fset(v_xs_x27_458_, v___x_442_, v___x_462_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v___x_463_);
v___x_465_ = v___x_446_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_config_433_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_extra_435_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_extraInj_436_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_extraFacts_437_);
lean_ctor_set(v_reuseFailAlloc_466_, 5, v_symPrios_438_);
lean_ctor_set(v_reuseFailAlloc_466_, 6, v_norm_439_);
lean_ctor_set(v_reuseFailAlloc_466_, 7, v_normProcs_440_);
lean_ctor_set(v_reuseFailAlloc_466_, 8, v_anchorRefs_x3f_441_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(lean_object* v_origin_479_, lean_object* v_as_480_, size_t v_sz_481_, size_t v_i_482_, lean_object* v_b_483_){
_start:
{
lean_object* v_a_485_; uint8_t v___x_489_; 
v___x_489_ = lean_usize_dec_lt(v_i_482_, v_sz_481_);
if (v___x_489_ == 0)
{
return v_b_483_;
}
else
{
lean_object* v_a_490_; lean_object* v_ematch_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_a_490_ = lean_array_uget_borrowed(v_as_480_, v_i_482_);
v_ematch_491_ = lean_ctor_get(v_a_490_, 3);
v___x_492_ = l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(v_ematch_491_, v_origin_479_);
v___x_493_ = l_List_isEmpty___redArg(v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
v___x_494_ = l_List_appendTR___redArg(v_b_483_, v___x_492_);
v_a_485_ = v___x_494_;
goto v___jp_484_;
}
else
{
lean_dec(v___x_492_);
v_a_485_ = v_b_483_;
goto v___jp_484_;
}
}
v___jp_484_:
{
size_t v___x_486_; size_t v___x_487_; 
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_i_482_, v___x_486_);
v_i_482_ = v___x_487_;
v_b_483_ = v_a_485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0___boxed(lean_object* v_origin_495_, lean_object* v_as_496_, lean_object* v_sz_497_, lean_object* v_i_498_, lean_object* v_b_499_){
_start:
{
size_t v_sz_boxed_500_; size_t v_i_boxed_501_; lean_object* v_res_502_; 
v_sz_boxed_500_ = lean_unbox_usize(v_sz_497_);
lean_dec(v_sz_497_);
v_i_boxed_501_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_495_, v_as_496_, v_sz_boxed_500_, v_i_boxed_501_, v_b_499_);
lean_dec_ref(v_as_496_);
lean_dec_ref(v_origin_495_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(lean_object* v_s_503_, lean_object* v_origin_504_){
_start:
{
lean_object* v_result_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v___x_508_; 
v_result_505_ = lean_box(0);
v_sz_506_ = lean_array_size(v_s_503_);
v___x_507_ = ((size_t)0ULL);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_504_, v_s_503_, v_sz_506_, v___x_507_, v_result_505_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor___boxed(lean_object* v_s_509_, lean_object* v_origin_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_509_, v_origin_510_);
lean_dec_ref(v_origin_510_);
lean_dec_ref(v_s_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(lean_object* v_upperBound_512_, lean_object* v_s_513_, lean_object* v_origin_514_, lean_object* v_a_515_, lean_object* v_b_516_){
_start:
{
lean_object* v_a_518_; uint8_t v___x_522_; 
v___x_522_ = lean_nat_dec_lt(v_a_515_, v_upperBound_512_);
if (v___x_522_ == 0)
{
lean_dec(v_a_515_);
return v_b_516_;
}
else
{
lean_object* v___x_523_; lean_object* v_ematch_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_523_ = lean_array_fget_borrowed(v_s_513_, v_a_515_);
v_ematch_524_ = lean_ctor_get(v___x_523_, 3);
v___x_525_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_ematch_524_, v_origin_514_);
v___x_526_ = l_List_isEmpty___redArg(v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
v___x_527_ = l_List_appendTR___redArg(v_b_516_, v___x_525_);
v_a_518_ = v___x_527_;
goto v___jp_517_;
}
else
{
lean_dec(v___x_525_);
v_a_518_ = v_b_516_;
goto v___jp_517_;
}
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_add(v_a_515_, v___x_519_);
lean_dec(v_a_515_);
v_a_515_ = v___x_520_;
v_b_516_ = v_a_518_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg___boxed(lean_object* v_upperBound_528_, lean_object* v_s_529_, lean_object* v_origin_530_, lean_object* v_a_531_, lean_object* v_b_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_528_, v_s_529_, v_origin_530_, v_a_531_, v_b_532_);
lean_dec_ref(v_origin_530_);
lean_dec_ref(v_s_529_);
lean_dec(v_upperBound_528_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find(lean_object* v_s_534_, lean_object* v_origin_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_r_538_; lean_object* v___x_539_; 
v___x_536_ = lean_array_get_size(v_s_534_);
v___x_537_ = lean_unsigned_to_nat(0u);
v_r_538_ = lean_box(0);
v___x_539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v___x_536_, v_s_534_, v_origin_535_, v___x_537_, v_r_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find___boxed(lean_object* v_s_540_, lean_object* v_origin_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Meta_Grind_ExtensionStateArray_find(v_s_540_, v_origin_541_);
lean_dec_ref(v_origin_541_);
lean_dec_ref(v_s_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(lean_object* v_upperBound_543_, lean_object* v_s_544_, lean_object* v_origin_545_, lean_object* v_inst_546_, lean_object* v_R_547_, lean_object* v_a_548_, lean_object* v_b_549_, lean_object* v_c_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_543_, v_s_544_, v_origin_545_, v_a_548_, v_b_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___boxed(lean_object* v_upperBound_552_, lean_object* v_s_553_, lean_object* v_origin_554_, lean_object* v_inst_555_, lean_object* v_R_556_, lean_object* v_a_557_, lean_object* v_b_558_, lean_object* v_c_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(v_upperBound_552_, v_s_553_, v_origin_554_, v_inst_555_, v_R_556_, v_a_557_, v_b_558_, v_c_559_);
lean_dec_ref(v_origin_554_);
lean_dec_ref(v_s_553_);
lean_dec(v_upperBound_552_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(lean_object* v_msgData_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; lean_object* v_env_568_; lean_object* v___x_569_; lean_object* v_toCold_570_; lean_object* v_mctx_571_; lean_object* v_lctx_572_; lean_object* v_options_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_567_ = lean_st_ref_get(v___y_565_);
v_env_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc_ref(v_env_568_);
lean_dec(v___x_567_);
v___x_569_ = lean_st_ref_get(v___y_563_);
v_toCold_570_ = lean_ctor_get(v___y_564_, 0);
v_mctx_571_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_mctx_571_);
lean_dec(v___x_569_);
v_lctx_572_ = lean_ctor_get(v___y_562_, 2);
v_options_573_ = lean_ctor_get(v_toCold_570_, 2);
lean_inc_ref(v_options_573_);
lean_inc_ref(v_lctx_572_);
v___x_574_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_574_, 0, v_env_568_);
lean_ctor_set(v___x_574_, 1, v_mctx_571_);
lean_ctor_set(v___x_574_, 2, v_lctx_572_);
lean_ctor_set(v___x_574_, 3, v_options_573_);
v___x_575_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_msgData_561_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msgData_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_583_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_584_, lean_object* v_opt_585_){
_start:
{
lean_object* v_name_586_; lean_object* v_defValue_587_; lean_object* v_map_588_; lean_object* v___x_589_; 
v_name_586_ = lean_ctor_get(v_opt_585_, 0);
v_defValue_587_ = lean_ctor_get(v_opt_585_, 1);
v_map_588_ = lean_ctor_get(v_opts_584_, 0);
v___x_589_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_588_, v_name_586_);
if (lean_obj_tag(v___x_589_) == 0)
{
uint8_t v___x_590_; 
v___x_590_ = lean_unbox(v_defValue_587_);
return v___x_590_;
}
else
{
lean_object* v_val_591_; 
v_val_591_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_val_591_);
lean_dec_ref_known(v___x_589_, 1);
if (lean_obj_tag(v_val_591_) == 1)
{
uint8_t v_v_592_; 
v_v_592_ = lean_ctor_get_uint8(v_val_591_, 0);
lean_dec_ref_known(v_val_591_, 0);
return v_v_592_;
}
else
{
uint8_t v___x_593_; 
lean_dec(v_val_591_);
v___x_593_ = lean_unbox(v_defValue_587_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_594_, lean_object* v_opt_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_opts_594_, v_opt_595_);
lean_dec_ref(v_opt_595_);
lean_dec_ref(v_opts_594_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_606_, uint8_t v___y_607_, lean_object* v_x_608_){
_start:
{
if (lean_obj_tag(v_x_608_) == 1)
{
lean_object* v_pre_609_; 
v_pre_609_ = lean_ctor_get(v_x_608_, 0);
switch(lean_obj_tag(v_pre_609_))
{
case 1:
{
lean_object* v_pre_610_; 
v_pre_610_ = lean_ctor_get(v_pre_609_, 0);
switch(lean_obj_tag(v_pre_610_))
{
case 0:
{
lean_object* v_str_611_; lean_object* v_str_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_str_611_ = lean_ctor_get(v_x_608_, 1);
v_str_612_ = lean_ctor_get(v_pre_609_, 1);
v___x_613_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_614_ = lean_string_dec_eq(v_str_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_616_ = lean_string_dec_eq(v_str_612_, v___x_615_);
if (v___x_616_ == 0)
{
return v___x_616_;
}
else
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_618_ = lean_string_dec_eq(v_str_611_, v___x_617_);
if (v___x_618_ == 0)
{
return v___x_618_;
}
else
{
return v_suppressElabErrors_606_;
}
}
}
else
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_620_ = lean_string_dec_eq(v_str_611_, v___x_619_);
if (v___x_620_ == 0)
{
return v___x_620_;
}
else
{
return v_suppressElabErrors_606_;
}
}
}
case 1:
{
lean_object* v_pre_621_; 
v_pre_621_ = lean_ctor_get(v_pre_610_, 0);
if (lean_obj_tag(v_pre_621_) == 0)
{
lean_object* v_str_622_; lean_object* v_str_623_; lean_object* v_str_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_str_622_ = lean_ctor_get(v_x_608_, 1);
v_str_623_ = lean_ctor_get(v_pre_609_, 1);
v_str_624_ = lean_ctor_get(v_pre_610_, 1);
v___x_625_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_626_ = lean_string_dec_eq(v_str_624_, v___x_625_);
if (v___x_626_ == 0)
{
return v___x_626_;
}
else
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_628_ = lean_string_dec_eq(v_str_623_, v___x_627_);
if (v___x_628_ == 0)
{
return v___x_628_;
}
else
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_630_ = lean_string_dec_eq(v_str_622_, v___x_629_);
if (v___x_630_ == 0)
{
return v___x_630_;
}
else
{
return v_suppressElabErrors_606_;
}
}
}
}
else
{
return v___y_607_;
}
}
default: 
{
return v___y_607_;
}
}
}
case 0:
{
lean_object* v_str_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_str_631_ = lean_ctor_get(v_x_608_, 1);
v___x_632_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_633_ = lean_string_dec_eq(v_str_631_, v___x_632_);
if (v___x_633_ == 0)
{
return v___x_633_;
}
else
{
return v_suppressElabErrors_606_;
}
}
default: 
{
return v___y_607_;
}
}
}
else
{
return v___y_607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_634_, lean_object* v___y_635_, lean_object* v_x_636_){
_start:
{
uint8_t v_suppressElabErrors_boxed_637_; uint8_t v___y_4539__boxed_638_; uint8_t v_res_639_; lean_object* v_r_640_; 
v_suppressElabErrors_boxed_637_ = lean_unbox(v_suppressElabErrors_634_);
v___y_4539__boxed_638_ = lean_unbox(v___y_635_);
v_res_639_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_637_, v___y_4539__boxed_638_, v_x_636_);
lean_dec(v_x_636_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_642_, lean_object* v_msgData_643_, uint8_t v_severity_644_, uint8_t v_isSilent_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
uint8_t v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; uint8_t v___y_658_; lean_object* v_toCold_659_; lean_object* v___y_660_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; uint8_t v___y_692_; lean_object* v___y_693_; uint8_t v___y_694_; uint8_t v___y_695_; lean_object* v___y_696_; lean_object* v___y_716_; uint8_t v___y_717_; lean_object* v___y_718_; uint8_t v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; lean_object* v___y_722_; uint8_t v___y_726_; uint8_t v___y_727_; uint8_t v___y_728_; uint8_t v___x_739_; uint8_t v___y_741_; uint8_t v___y_742_; uint8_t v___y_743_; uint8_t v___y_745_; uint8_t v___x_753_; 
v___x_739_ = 2;
v___x_753_ = l_Lean_instBEqMessageSeverity_beq(v_severity_644_, v___x_739_);
if (v___x_753_ == 0)
{
v___y_745_ = v___x_753_;
goto v___jp_744_;
}
else
{
uint8_t v___x_754_; 
lean_inc_ref(v_msgData_643_);
v___x_754_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_643_);
v___y_745_ = v___x_754_;
goto v___jp_744_;
}
v___jp_651_:
{
lean_object* v_currNamespace_661_; lean_object* v_openDecls_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v_env_667_; lean_object* v_nextMacroScope_668_; lean_object* v_ngen_669_; lean_object* v_auxDeclNGen_670_; lean_object* v_traceState_671_; lean_object* v_cache_672_; lean_object* v_recordedDeps_673_; lean_object* v_messages_674_; lean_object* v_infoState_675_; lean_object* v_snapshotTasks_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_687_; 
v_currNamespace_661_ = lean_ctor_get(v_toCold_659_, 4);
v_openDecls_662_ = lean_ctor_get(v_toCold_659_, 5);
lean_inc(v_openDecls_662_);
lean_inc(v_currNamespace_661_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v_currNamespace_661_);
lean_ctor_set(v___x_663_, 1, v_openDecls_662_);
v___x_664_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___y_656_);
lean_inc_ref(v___y_655_);
lean_inc_ref(v___y_653_);
v___x_665_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_665_, 0, v___y_653_);
lean_ctor_set(v___x_665_, 1, v___y_654_);
lean_ctor_set(v___x_665_, 2, v___y_657_);
lean_ctor_set(v___x_665_, 3, v___y_655_);
lean_ctor_set(v___x_665_, 4, v___x_664_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*5, v___y_652_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*5 + 1, v___y_658_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*5 + 2, v_isSilent_645_);
v___x_666_ = lean_st_ref_take(v___y_660_);
v_env_667_ = lean_ctor_get(v___x_666_, 0);
v_nextMacroScope_668_ = lean_ctor_get(v___x_666_, 1);
v_ngen_669_ = lean_ctor_get(v___x_666_, 2);
v_auxDeclNGen_670_ = lean_ctor_get(v___x_666_, 3);
v_traceState_671_ = lean_ctor_get(v___x_666_, 4);
v_cache_672_ = lean_ctor_get(v___x_666_, 5);
v_recordedDeps_673_ = lean_ctor_get(v___x_666_, 6);
v_messages_674_ = lean_ctor_get(v___x_666_, 7);
v_infoState_675_ = lean_ctor_get(v___x_666_, 8);
v_snapshotTasks_676_ = lean_ctor_get(v___x_666_, 9);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_687_ == 0)
{
v___x_678_ = v___x_666_;
v_isShared_679_ = v_isSharedCheck_687_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snapshotTasks_676_);
lean_inc(v_infoState_675_);
lean_inc(v_messages_674_);
lean_inc(v_recordedDeps_673_);
lean_inc(v_cache_672_);
lean_inc(v_traceState_671_);
lean_inc(v_auxDeclNGen_670_);
lean_inc(v_ngen_669_);
lean_inc(v_nextMacroScope_668_);
lean_inc(v_env_667_);
lean_dec(v___x_666_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_687_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_680_ = lean_box(0);
v___x_681_ = l_Lean_MessageLog_add(v___x_665_, v_messages_674_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 7, v___x_681_);
v___x_683_ = v___x_678_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_env_667_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_nextMacroScope_668_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_ngen_669_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_auxDeclNGen_670_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v_traceState_671_);
lean_ctor_set(v_reuseFailAlloc_686_, 5, v_cache_672_);
lean_ctor_set(v_reuseFailAlloc_686_, 6, v_recordedDeps_673_);
lean_ctor_set(v_reuseFailAlloc_686_, 7, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_686_, 8, v_infoState_675_);
lean_ctor_set(v_reuseFailAlloc_686_, 9, v_snapshotTasks_676_);
v___x_683_ = v_reuseFailAlloc_686_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_st_ref_put(v___y_660_, v___x_683_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_680_);
return v___x_685_;
}
}
}
v___jp_688_:
{
lean_object* v_fileName_697_; lean_object* v_fileMap_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_714_; 
v_fileName_697_ = lean_ctor_get(v___y_693_, 0);
v_fileMap_698_ = lean_ctor_get(v___y_693_, 1);
v___x_699_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_643_);
v___x_700_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_699_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_714_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_714_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_714_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_inc_ref_n(v_fileMap_698_, 2);
v___x_705_ = l_Lean_FileMap_toPosition(v_fileMap_698_, v___y_691_);
lean_dec(v___y_691_);
v___x_706_ = l_Lean_FileMap_toPosition(v_fileMap_698_, v___y_696_);
lean_dec(v___y_696_);
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
v___x_708_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_694_ == 0)
{
lean_del_object(v___x_703_);
lean_dec_ref(v___y_690_);
v___y_652_ = v___y_692_;
v___y_653_ = v_fileName_697_;
v___y_654_ = v___x_705_;
v___y_655_ = v___x_708_;
v___y_656_ = v_a_701_;
v___y_657_ = v___x_707_;
v___y_658_ = v___y_695_;
v_toCold_659_ = v___y_689_;
v___y_660_ = v___y_649_;
goto v___jp_651_;
}
else
{
uint8_t v___x_709_; 
lean_inc(v_a_701_);
v___x_709_ = l_Lean_MessageData_hasTag(v___y_690_, v_a_701_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_712_; 
lean_dec_ref_known(v___x_707_, 1);
lean_dec_ref(v___x_705_);
lean_dec(v_a_701_);
v___x_710_ = lean_box(0);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_710_);
v___x_712_ = v___x_703_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
else
{
lean_del_object(v___x_703_);
v___y_652_ = v___y_692_;
v___y_653_ = v_fileName_697_;
v___y_654_ = v___x_705_;
v___y_655_ = v___x_708_;
v___y_656_ = v_a_701_;
v___y_657_ = v___x_707_;
v___y_658_ = v___y_695_;
v_toCold_659_ = v___y_689_;
v___y_660_ = v___y_649_;
goto v___jp_651_;
}
}
}
}
v___jp_715_:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_Syntax_getTailPos_x3f(v___y_720_, v___y_719_);
lean_dec(v___y_720_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_inc(v___y_722_);
v___y_689_ = v___y_716_;
v___y_690_ = v___y_718_;
v___y_691_ = v___y_722_;
v___y_692_ = v___y_719_;
v___y_693_ = v___y_716_;
v___y_694_ = v___y_717_;
v___y_695_ = v___y_721_;
v___y_696_ = v___y_722_;
goto v___jp_688_;
}
else
{
lean_object* v_val_724_; 
v_val_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_val_724_);
lean_dec_ref_known(v___x_723_, 1);
v___y_689_ = v___y_716_;
v___y_690_ = v___y_718_;
v___y_691_ = v___y_722_;
v___y_692_ = v___y_719_;
v___y_693_ = v___y_716_;
v___y_694_ = v___y_717_;
v___y_695_ = v___y_721_;
v___y_696_ = v_val_724_;
goto v___jp_688_;
}
}
v___jp_725_:
{
lean_object* v_toCold_729_; lean_object* v_ref_730_; uint8_t v_suppressElabErrors_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___f_734_; lean_object* v_ref_735_; lean_object* v___x_736_; 
v_toCold_729_ = lean_ctor_get(v___y_648_, 0);
v_ref_730_ = lean_ctor_get(v___y_648_, 2);
v_suppressElabErrors_731_ = lean_ctor_get_uint8(v___y_648_, sizeof(void*)*3 + 2);
v___x_732_ = lean_box(v_suppressElabErrors_731_);
v___x_733_ = lean_box(v___y_726_);
v___f_734_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_734_, 0, v___x_732_);
lean_closure_set(v___f_734_, 1, v___x_733_);
v_ref_735_ = l_Lean_replaceRef(v_ref_642_, v_ref_730_);
v___x_736_ = l_Lean_Syntax_getPos_x3f(v_ref_735_, v___y_727_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_737_; 
v___x_737_ = lean_unsigned_to_nat(0u);
v___y_716_ = v_toCold_729_;
v___y_717_ = v_suppressElabErrors_731_;
v___y_718_ = v___f_734_;
v___y_719_ = v___y_727_;
v___y_720_ = v_ref_735_;
v___y_721_ = v___y_728_;
v___y_722_ = v___x_737_;
goto v___jp_715_;
}
else
{
lean_object* v_val_738_; 
v_val_738_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_val_738_);
lean_dec_ref_known(v___x_736_, 1);
v___y_716_ = v_toCold_729_;
v___y_717_ = v_suppressElabErrors_731_;
v___y_718_ = v___f_734_;
v___y_719_ = v___y_727_;
v___y_720_ = v_ref_735_;
v___y_721_ = v___y_728_;
v___y_722_ = v_val_738_;
goto v___jp_715_;
}
}
v___jp_740_:
{
if (v___y_743_ == 0)
{
v___y_726_ = v___y_741_;
v___y_727_ = v___y_742_;
v___y_728_ = v_severity_644_;
goto v___jp_725_;
}
else
{
v___y_726_ = v___y_741_;
v___y_727_ = v___y_742_;
v___y_728_ = v___x_739_;
goto v___jp_725_;
}
}
v___jp_744_:
{
if (v___y_745_ == 0)
{
uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = 1;
v___x_747_ = l_Lean_instBEqMessageSeverity_beq(v_severity_644_, v___x_746_);
if (v___x_747_ == 0)
{
v___y_741_ = v___y_745_;
v___y_742_ = v___y_745_;
v___y_743_ = v___x_747_;
goto v___jp_740_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_648_);
v___x_749_ = l_Lean_warningAsError;
v___x_750_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_748_, v___x_749_);
lean_dec_ref(v___x_748_);
v___y_741_ = v___y_745_;
v___y_742_ = v___y_745_;
v___y_743_ = v___x_750_;
goto v___jp_740_;
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec_ref(v_msgData_643_);
v___x_751_ = lean_box(0);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_755_, lean_object* v_msgData_756_, lean_object* v_severity_757_, lean_object* v_isSilent_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
uint8_t v_severity_boxed_764_; uint8_t v_isSilent_boxed_765_; lean_object* v_res_766_; 
v_severity_boxed_764_ = lean_unbox(v_severity_757_);
v_isSilent_boxed_765_ = lean_unbox(v_isSilent_758_);
v_res_766_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_755_, v_msgData_756_, v_severity_boxed_764_, v_isSilent_boxed_765_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v_ref_755_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* v_msgData_767_, uint8_t v_severity_768_, uint8_t v_isSilent_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_ref_775_; lean_object* v___x_776_; 
v_ref_775_ = lean_ctor_get(v___y_772_, 2);
v___x_776_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_775_, v_msgData_767_, v_severity_768_, v_isSilent_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* v_msgData_777_, lean_object* v_severity_778_, lean_object* v_isSilent_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
uint8_t v_severity_boxed_785_; uint8_t v_isSilent_boxed_786_; lean_object* v_res_787_; 
v_severity_boxed_785_ = lean_unbox(v_severity_778_);
v_isSilent_boxed_786_ = lean_unbox(v_isSilent_779_);
v_res_787_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_777_, v_severity_boxed_785_, v_isSilent_boxed_786_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* v_msgData_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
uint8_t v___x_794_; uint8_t v___x_795_; lean_object* v___x_796_; 
v___x_794_ = 1;
v___x_795_ = 0;
v___x_796_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_788_, v___x_794_, v___x_795_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* v_msgData_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_803_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
if (lean_obj_tag(v_a_807_) == 0)
{
lean_object* v___x_809_; 
v___x_809_ = l_List_reverse___redArg(v_a_808_);
return v___x_809_;
}
else
{
lean_object* v_head_810_; lean_object* v_tail_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_824_; 
v_head_810_ = lean_ctor_get(v_a_807_, 0);
v_tail_811_ = lean_ctor_get(v_a_807_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_a_807_);
if (v_isSharedCheck_824_ == 0)
{
v___x_813_ = v_a_807_;
v_isShared_814_ = v_isSharedCheck_824_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_tail_811_);
lean_inc(v_head_810_);
lean_dec(v_a_807_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_824_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
uint8_t v_minIndexable_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v_minIndexable_815_ = 0;
v___x_816_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_817_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_810_, v_minIndexable_815_);
lean_dec(v_head_810_);
v___x_818_ = l_Lean_stringToMessageData(v___x_817_);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_816_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v_a_808_);
lean_ctor_set(v___x_813_, 0, v___x_819_);
v___x_821_ = v___x_813_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_a_808_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
v_a_807_ = v_tail_811_;
v_a_808_ = v___x_821_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
if (lean_obj_tag(v_a_825_) == 0)
{
lean_object* v___x_827_; 
v___x_827_ = l_List_reverse___redArg(v_a_826_);
return v___x_827_;
}
else
{
lean_object* v_head_828_; lean_object* v_tail_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_837_; 
v_head_828_ = lean_ctor_get(v_a_825_, 0);
v_tail_829_ = lean_ctor_get(v_a_825_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v_a_825_);
if (v_isSharedCheck_837_ == 0)
{
v___x_831_ = v_a_825_;
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_tail_829_);
lean_inc(v_head_828_);
lean_dec(v_a_825_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v_a_826_);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_head_828_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_a_826_);
v___x_834_ = v_reuseFailAlloc_836_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
v_a_825_ = v_tail_829_;
v_a_826_ = v___x_834_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
v___x_840_ = l_Lean_stringToMessageData(v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
v___x_843_ = l_Lean_stringToMessageData(v___x_842_);
return v___x_843_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
v___x_846_ = l_Lean_stringToMessageData(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* v_s_847_, lean_object* v_declName_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_kinds_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v_ks_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___x_879_; lean_object* v___x_880_; 
lean_inc(v_declName_848_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v_declName_848_);
v___x_880_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_847_, v___x_879_);
lean_dec_ref_known(v___x_879_, 1);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec(v_declName_848_);
v___x_881_ = lean_box(0);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
else
{
lean_object* v_head_883_; lean_object* v_tail_884_; uint8_t v_minIndexable_885_; uint8_t v_gen_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; 
v_head_883_ = lean_ctor_get(v___x_880_, 0);
v_tail_884_ = lean_ctor_get(v___x_880_, 1);
v_minIndexable_885_ = 0;
if (lean_obj_tag(v_tail_884_) == 0)
{
lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_906_; 
lean_inc(v_head_883_);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; lean_object* v_unused_908_; 
v_unused_907_ = lean_ctor_get(v___x_880_, 1);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v___x_880_, 0);
lean_dec(v_unused_908_);
v___x_898_ = v___x_880_;
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
else
{
lean_dec(v___x_880_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_900_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_901_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_883_, v_minIndexable_885_);
lean_dec(v_head_883_);
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
if (v_isShared_899_ == 0)
{
lean_ctor_set_tag(v___x_898_, 7);
lean_ctor_set(v___x_898_, 1, v___x_902_);
lean_ctor_set(v___x_898_, 0, v___x_900_);
v___x_904_ = v___x_898_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
v_kinds_855_ = v___x_904_;
v___y_856_ = v_a_849_;
v___y_857_ = v_a_850_;
v___y_858_ = v_a_851_;
v___y_859_ = v_a_852_;
goto v___jp_854_;
}
}
}
else
{
lean_object* v_head_909_; 
v_head_909_ = lean_ctor_get(v_tail_884_, 0);
switch(lean_obj_tag(v_head_909_))
{
case 1:
{
lean_object* v_tail_910_; 
v_tail_910_ = lean_ctor_get(v_tail_884_, 1);
if (lean_obj_tag(v_tail_910_) == 0)
{
if (lean_obj_tag(v_head_883_) == 0)
{
uint8_t v_gen_911_; 
lean_inc_ref(v_head_883_);
lean_dec_ref_known(v___x_880_, 2);
v_gen_911_ = lean_ctor_get_uint8(v_head_883_, 0);
lean_dec_ref_known(v_head_883_, 0);
v_gen_887_ = v_gen_911_;
v___y_888_ = v_a_849_;
v___y_889_ = v_a_850_;
v___y_890_ = v_a_851_;
v___y_891_ = v_a_852_;
goto v___jp_886_;
}
else
{
v_ks_870_ = v___x_880_;
v___y_871_ = v_a_849_;
v___y_872_ = v_a_850_;
v___y_873_ = v_a_851_;
v___y_874_ = v_a_852_;
goto v___jp_869_;
}
}
else
{
v_ks_870_ = v___x_880_;
v___y_871_ = v_a_849_;
v___y_872_ = v_a_850_;
v___y_873_ = v_a_851_;
v___y_874_ = v_a_852_;
goto v___jp_869_;
}
}
case 0:
{
lean_object* v_tail_912_; 
v_tail_912_ = lean_ctor_get(v_tail_884_, 1);
if (lean_obj_tag(v_tail_912_) == 0)
{
if (lean_obj_tag(v_head_883_) == 1)
{
uint8_t v_gen_913_; 
lean_inc_ref(v_head_883_);
lean_dec_ref_known(v___x_880_, 2);
v_gen_913_ = lean_ctor_get_uint8(v_head_883_, 0);
lean_dec_ref_known(v_head_883_, 0);
v_gen_887_ = v_gen_913_;
v___y_888_ = v_a_849_;
v___y_889_ = v_a_850_;
v___y_890_ = v_a_851_;
v___y_891_ = v_a_852_;
goto v___jp_886_;
}
else
{
v_ks_870_ = v___x_880_;
v___y_871_ = v_a_849_;
v___y_872_ = v_a_850_;
v___y_873_ = v_a_851_;
v___y_874_ = v_a_852_;
goto v___jp_869_;
}
}
else
{
v_ks_870_ = v___x_880_;
v___y_871_ = v_a_849_;
v___y_872_ = v_a_850_;
v___y_873_ = v_a_851_;
v___y_874_ = v_a_852_;
goto v___jp_869_;
}
}
default: 
{
v_ks_870_ = v___x_880_;
v___y_871_ = v_a_849_;
v___y_872_ = v_a_850_;
v___y_873_ = v_a_851_;
v___y_874_ = v_a_852_;
goto v___jp_869_;
}
}
}
v___jp_886_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_892_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_893_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_893_, 0, v_gen_887_);
v___x_894_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v___x_893_, v_minIndexable_885_);
lean_dec_ref_known(v___x_893_, 0);
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_892_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v_kinds_855_ = v___x_896_;
v___y_856_ = v___y_888_;
v___y_857_ = v___y_889_;
v___y_858_ = v___y_890_;
v___y_859_ = v___y_891_;
goto v___jp_854_;
}
}
v___jp_854_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_860_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
v___x_861_ = l_Lean_MessageData_ofName(v_declName_848_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v_kinds_855_);
v___x_866_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v___x_867_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_868_;
}
v___jp_869_:
{
lean_object* v___x_875_; lean_object* v_ks_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_875_ = lean_box(0);
v_ks_876_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(v_ks_870_, v___x_875_);
v___x_877_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(v_ks_876_, v___x_875_);
v___x_878_ = l_Lean_MessageData_ofList(v___x_877_);
v_kinds_855_ = v___x_878_;
v___y_856_ = v___y_871_;
v___y_857_ = v___y_872_;
v___y_858_ = v___y_873_;
v___y_859_ = v___y_874_;
goto v___jp_854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* v_s_914_, lean_object* v_declName_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_914_, v_declName_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec_ref(v_s_914_);
return v_res_921_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_922_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
lean_ctor_set(v___x_927_, 2, v___x_926_);
lean_ctor_set(v___x_927_, 3, v___x_926_);
lean_ctor_set(v___x_927_, 4, v___x_925_);
lean_ctor_set(v___x_927_, 5, v___x_925_);
lean_ctor_set(v___x_927_, 6, v___x_925_);
lean_ctor_set(v___x_927_, 7, v___x_925_);
lean_ctor_set(v___x_927_, 8, v___x_925_);
lean_ctor_set(v___x_927_, 9, v___x_925_);
lean_ctor_set(v___x_927_, 10, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_unsigned_to_nat(32u);
v___x_929_ = lean_mk_empty_array_with_capacity(v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_931_ = ((size_t)5ULL);
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = lean_unsigned_to_nat(32u);
v___x_934_ = lean_mk_empty_array_with_capacity(v___x_933_);
v___x_935_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
v___x_936_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_934_);
lean_ctor_set(v___x_936_, 2, v___x_932_);
lean_ctor_set(v___x_936_, 3, v___x_932_);
lean_ctor_set_usize(v___x_936_, 4, v___x_931_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_937_ = lean_box(1);
v___x_938_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
v___x_939_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___x_938_);
lean_ctor_set(v___x_940_, 2, v___x_937_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* v_msgData_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v_toCold_946_; lean_object* v_env_947_; lean_object* v_options_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_945_ = lean_st_ref_get(v___y_943_);
v_toCold_946_ = lean_ctor_get(v___y_942_, 0);
v_env_947_ = lean_ctor_get(v___x_945_, 0);
lean_inc_ref(v_env_947_);
lean_dec(v___x_945_);
v_options_948_ = lean_ctor_get(v_toCold_946_, 2);
v___x_949_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_950_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_948_);
v___x_951_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_951_, 0, v_env_947_);
lean_ctor_set(v___x_951_, 1, v___x_949_);
lean_ctor_set(v___x_951_, 2, v___x_950_);
lean_ctor_set(v___x_951_, 3, v_options_948_);
v___x_952_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v_msgData_941_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object* v_msgData_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msgData_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_ref_963_; lean_object* v___x_964_; lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_973_; 
v_ref_963_ = lean_ctor_get(v___y_960_, 2);
v___x_964_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msg_959_, v___y_960_, v___y_961_);
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_973_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
lean_inc(v_ref_963_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v_ref_963_);
lean_ctor_set(v___x_969_, 1, v_a_965_);
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 1);
lean_ctor_set(v___x_967_, 0, v___x_969_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_978_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object* v_s_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_996_; lean_object* v_env_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_996_ = lean_st_ref_get(v_a_994_);
v_env_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc_ref(v_env_997_);
lean_dec(v___x_996_);
v___x_998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
v___x_999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5));
lean_inc_ref(v_s_992_);
v___x_1000_ = l_Lean_Parser_runParserCategory(v_env_997_, v___x_998_, v_s_992_, v___x_999_);
if (lean_obj_tag(v___x_1000_) == 1)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
lean_dec_ref(v_s_992_);
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_Meta_Grind_getAttrKindCore(v_a_1001_, v_a_993_, v_a_994_);
return v___x_1002_;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec_ref(v___x_1000_);
v___x_1003_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7);
v___x_1004_ = l_Lean_stringToMessageData(v_s_992_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1005_, v_a_993_, v_a_994_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object* v_s_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(v_s_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object* v_00_u03b1_1012_, lean_object* v_msg_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_1013_, v___y_1014_, v___y_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object* v_00_u03b1_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(v_00_u03b1_1018_, v_msg_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object* v_msg_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_ref_1030_; lean_object* v___x_1031_; lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
v_ref_1030_ = lean_ctor_get(v___y_1027_, 2);
v___x_1031_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_inc(v_ref_1030_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_ref_1030_);
lean_ctor_set(v___x_1036_, 1, v_a_1032_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 1);
lean_ctor_set(v___x_1034_, 0, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object* v_msg_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1047_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t v_minIndexable_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
if (v_minIndexable_1051_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1);
v___x_1060_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1059_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object* v_minIndexable_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
uint8_t v_minIndexable_boxed_1067_; lean_object* v_res_1068_; 
v_minIndexable_boxed_1067_ = lean_unbox(v_minIndexable_1061_);
v_res_1068_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_boxed_1067_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object* v_00_u03b1_1069_, lean_object* v_msg_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object* v_00_u03b1_1077_, lean_object* v_msg_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(v_00_u03b1_1077_, v_msg_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1093_ = l_Lean_stringToMessageData(v___x_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1096_ = l_Lean_stringToMessageData(v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1099_ = l_Lean_stringToMessageData(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1106_, lean_object* v_declHint_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_env_1112_; uint8_t v___x_1113_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_st_ref_get(v___y_1108_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = l_Lean_Name_isAnonymous(v_declHint_1107_);
if (v___x_1113_ == 0)
{
uint8_t v_isExporting_1114_; 
v_isExporting_1114_ = lean_ctor_get_uint8(v_env_1112_, sizeof(void*)*8);
if (v_isExporting_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec_ref(v_env_1112_);
lean_dec(v_declHint_1107_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v_msg_1106_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
lean_inc_ref(v_env_1112_);
v___x_1116_ = l_Lean_Environment_setExporting(v_env_1112_, v___x_1113_);
lean_inc(v_declHint_1107_);
lean_inc_ref(v___x_1116_);
v___x_1117_ = l_Lean_Environment_contains(v___x_1116_, v_declHint_1107_, v_isExporting_1114_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_env_1112_);
lean_dec(v_declHint_1107_);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_msg_1106_);
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v_c_1124_; lean_object* v___x_1125_; 
v___x_1119_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_1120_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
v___x_1121_ = l_Lean_Options_empty;
v___x_1122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1116_);
lean_ctor_set(v___x_1122_, 1, v___x_1119_);
lean_ctor_set(v___x_1122_, 2, v___x_1120_);
lean_ctor_set(v___x_1122_, 3, v___x_1121_);
lean_inc(v_declHint_1107_);
v___x_1123_ = l_Lean_MessageData_ofConstName(v_declHint_1107_, v___x_1113_);
v_c_1124_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1124_, 0, v___x_1122_);
lean_ctor_set(v_c_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1112_, v_declHint_1107_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec_ref(v_env_1112_);
lean_dec(v_declHint_1107_);
v___x_1126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
lean_ctor_set(v___x_1127_, 1, v_c_1124_);
v___x_1128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_MessageData_note(v___x_1129_);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_msg_1106_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
else
{
lean_object* v_val_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1167_; 
v_val_1133_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1135_ = v___x_1125_;
v_isShared_1136_ = v_isSharedCheck_1167_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_val_1133_);
lean_dec(v___x_1125_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1167_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v_mod_1139_; uint8_t v___x_1140_; 
v___x_1137_ = l_Lean_Environment_header(v_env_1112_);
lean_dec_ref(v_env_1112_);
v___x_1138_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1137_);
v_mod_1139_ = lean_array_get(v___x_1110_, v___x_1138_, v_val_1133_);
lean_dec(v_val_1133_);
lean_dec_ref(v___x_1138_);
v___x_1140_ = l_Lean_isPrivateName(v_declHint_1107_);
lean_dec(v_declHint_1107_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v_c_1124_);
v___x_1143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = l_Lean_MessageData_ofName(v_mod_1139_);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_MessageData_note(v___x_1148_);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v_msg_1106_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1150_);
v___x_1152_ = v___x_1135_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1154_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v_c_1124_);
v___x_1156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_MessageData_ofName(v_mod_1139_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = l_Lean_MessageData_note(v___x_1161_);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_msg_1106_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1163_);
v___x_1165_ = v___x_1135_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1168_; 
lean_dec_ref(v_env_1112_);
lean_dec(v_declHint_1107_);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_msg_1106_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1169_, lean_object* v_declHint_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1169_, v_declHint_1170_, v___y_1171_);
lean_dec(v___y_1171_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1174_, lean_object* v_declHint_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1191_; 
v___x_1181_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1174_, v_declHint_1175_, v___y_1179_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1186_ = l_Lean_unknownIdentifierMessageTag;
v___x_1187_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v_a_1182_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1187_);
v___x_1189_ = v___x_1184_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1192_, lean_object* v_declHint_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1192_, v_declHint_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1200_, lean_object* v_msg_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_toCold_1207_; lean_object* v_currRecDepth_1208_; lean_object* v_ref_1209_; uint16_t v_optionFlags_1210_; uint8_t v_suppressElabErrors_1211_; uint8_t v_isRecordingDeps_1212_; lean_object* v_ref_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_toCold_1207_ = lean_ctor_get(v___y_1204_, 0);
v_currRecDepth_1208_ = lean_ctor_get(v___y_1204_, 1);
v_ref_1209_ = lean_ctor_get(v___y_1204_, 2);
v_optionFlags_1210_ = lean_ctor_get_uint16(v___y_1204_, sizeof(void*)*3);
v_suppressElabErrors_1211_ = lean_ctor_get_uint8(v___y_1204_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1212_ = lean_ctor_get_uint8(v___y_1204_, sizeof(void*)*3 + 3);
v_ref_1213_ = l_Lean_replaceRef(v_ref_1200_, v_ref_1209_);
lean_inc(v_currRecDepth_1208_);
lean_inc_ref(v_toCold_1207_);
v___x_1214_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1214_, 0, v_toCold_1207_);
lean_ctor_set(v___x_1214_, 1, v_currRecDepth_1208_);
lean_ctor_set(v___x_1214_, 2, v_ref_1213_);
lean_ctor_set_uint16(v___x_1214_, sizeof(void*)*3, v_optionFlags_1210_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*3 + 2, v_suppressElabErrors_1211_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*3 + 3, v_isRecordingDeps_1212_);
v___x_1215_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1201_, v___y_1202_, v___y_1203_, v___x_1214_, v___y_1205_);
lean_dec_ref_known(v___x_1214_, 3);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1216_, lean_object* v_msg_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1216_, v_msg_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v_ref_1216_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1224_, lean_object* v_msg_1225_, lean_object* v_declHint_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; lean_object* v_a_1233_; lean_object* v___x_1234_; 
v___x_1232_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1225_, v_declHint_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1224_, v_a_1233_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1235_, lean_object* v_msg_1236_, lean_object* v_declHint_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1235_, v_msg_1236_, v_declHint_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v_ref_1235_);
return v_res_1243_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1246_ = l_Lean_stringToMessageData(v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1247_, lean_object* v_constName_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1254_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1255_ = 0;
lean_inc(v_constName_1248_);
v___x_1256_ = l_Lean_MessageData_ofConstName(v_constName_1248_, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1254_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1247_, v___x_1259_, v_constName_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1261_, lean_object* v_constName_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1261_, v_constName_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v_ref_1261_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_ref_1275_; lean_object* v___x_1276_; 
v_ref_1275_ = lean_ctor_get(v___y_1272_, 2);
v___x_1276_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1275_, v_constName_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1284_, uint8_t v_skipRealize_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v_env_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_st_ref_get(v___y_1289_);
v_env_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc_ref(v_env_1292_);
lean_dec(v___x_1291_);
lean_inc(v_constName_1284_);
v___x_1293_ = l_Lean_Environment_findAsync_x3f(v_env_1292_, v_constName_1284_, v_skipRealize_1285_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1284_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1294_;
}
else
{
lean_object* v_val_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_constName_1284_);
v_val_1295_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1293_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_val_1295_);
lean_dec(v___x_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set_tag(v___x_1297_, 0);
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1303_, lean_object* v_skipRealize_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
uint8_t v_skipRealize_boxed_1310_; lean_object* v_res_1311_; 
v_skipRealize_boxed_1310_ = lean_unbox(v_skipRealize_1304_);
v_res_1311_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1303_, v_skipRealize_boxed_1310_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___x_1315_; lean_object* v_env_1316_; uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1315_ = lean_st_ref_get(v___y_1313_);
v_env_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc_ref(v_env_1316_);
lean_dec(v___x_1315_);
v___x_1317_ = l_Lean_getReducibilityStatusCore(v_env_1316_, v_declName_1312_);
v___x_1318_ = lean_box(v___x_1317_);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1320_, v___y_1321_);
lean_dec(v___y_1321_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1346_; 
v___x_1330_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1324_, v___y_1328_);
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1346_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1346_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
uint8_t v___x_1335_; 
v___x_1335_ = lean_unbox(v_a_1331_);
lean_dec(v_a_1331_);
if (v___x_1335_ == 0)
{
uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1336_ = 1;
v___x_1337_ = lean_box(v___x_1336_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1337_);
v___x_1339_ = v___x_1333_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
else
{
uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1341_ = 0;
v___x_1342_ = lean_box(v___x_1341_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1342_);
v___x_1344_ = v___x_1333_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
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
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1353_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1362_ = l_Lean_stringToMessageData(v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1365_ = l_Lean_stringToMessageData(v___x_1364_);
return v___x_1365_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1368_ = l_Lean_stringToMessageData(v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1369_, lean_object* v_id_1370_, lean_object* v_declName_1371_, lean_object* v_kind_1372_, uint8_t v_minIndexable_1373_, uint8_t v_suggest_1374_, uint8_t v_warn_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v___y_1382_; lean_object* v_thm_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; uint8_t v___x_1437_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___x_1634_; 
v___x_1437_ = 0;
lean_inc(v_declName_1371_);
v___x_1634_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1371_, v___x_1437_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; uint8_t v_kind_1636_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v_kind_1636_ = lean_ctor_get_uint8(v_a_1635_, sizeof(void*)*3);
lean_dec(v_a_1635_);
switch(v_kind_1636_)
{
case 1:
{
v___y_1565_ = v_a_1376_;
v___y_1566_ = v_a_1377_;
v___y_1567_ = v_a_1378_;
v___y_1568_ = v_a_1379_;
goto v___jp_1564_;
}
case 2:
{
v___y_1565_ = v_a_1376_;
v___y_1566_ = v_a_1377_;
v___y_1567_ = v_a_1378_;
v___y_1568_ = v_a_1379_;
goto v___jp_1564_;
}
case 6:
{
v___y_1565_ = v_a_1376_;
v___y_1566_ = v_a_1377_;
v___y_1567_ = v_a_1378_;
v___y_1568_ = v_a_1379_;
goto v___jp_1564_;
}
case 0:
{
lean_object* v___x_1637_; 
lean_dec(v_id_1370_);
lean_inc(v_declName_1371_);
v___x_1637_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1371_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; uint8_t v___x_1639_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1639_ = lean_unbox(v_a_1638_);
lean_dec(v_a_1638_);
if (v___x_1639_ == 0)
{
v___y_1495_ = v_a_1376_;
v___y_1496_ = v_a_1377_;
v___y_1497_ = v_a_1378_;
v___y_1498_ = v_a_1379_;
goto v___jp_1494_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v_kind_1372_);
lean_dec_ref(v_params_1369_);
v___x_1640_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1641_ = l_Lean_MessageData_ofConstName(v_declName_1371_, v___x_1437_);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1644_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v_kind_1372_);
lean_dec(v_declName_1371_);
lean_dec_ref(v_params_1369_);
v_a_1654_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1637_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1637_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
default: 
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec(v_kind_1372_);
lean_dec(v_id_1370_);
lean_dec_ref(v_params_1369_);
v___x_1662_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1663_ = l_Lean_MessageData_ofConstName(v_declName_1371_, v___x_1437_);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1666_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_);
return v___x_1667_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v_kind_1372_);
lean_dec(v_declName_1371_);
lean_dec(v_id_1370_);
lean_dec_ref(v_params_1369_);
v_a_1668_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1634_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1634_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
v___jp_1381_:
{
lean_object* v_config_1383_; lean_object* v_extensions_1384_; lean_object* v_extra_1385_; lean_object* v_extraInj_1386_; lean_object* v_extraFacts_1387_; lean_object* v_symPrios_1388_; lean_object* v_norm_1389_; lean_object* v_normProcs_1390_; lean_object* v_anchorRefs_x3f_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1400_; 
v_config_1383_ = lean_ctor_get(v_params_1369_, 0);
v_extensions_1384_ = lean_ctor_get(v_params_1369_, 1);
v_extra_1385_ = lean_ctor_get(v_params_1369_, 2);
v_extraInj_1386_ = lean_ctor_get(v_params_1369_, 3);
v_extraFacts_1387_ = lean_ctor_get(v_params_1369_, 4);
v_symPrios_1388_ = lean_ctor_get(v_params_1369_, 5);
v_norm_1389_ = lean_ctor_get(v_params_1369_, 6);
v_normProcs_1390_ = lean_ctor_get(v_params_1369_, 7);
v_anchorRefs_x3f_1391_ = lean_ctor_get(v_params_1369_, 8);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_params_1369_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1393_ = v_params_1369_;
v_isShared_1394_ = v_isSharedCheck_1400_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_anchorRefs_x3f_1391_);
lean_inc(v_normProcs_1390_);
lean_inc(v_norm_1389_);
lean_inc(v_symPrios_1388_);
lean_inc(v_extraFacts_1387_);
lean_inc(v_extraInj_1386_);
lean_inc(v_extra_1385_);
lean_inc(v_extensions_1384_);
lean_inc(v_config_1383_);
lean_dec(v_params_1369_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1400_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1395_ = l_Lean_PersistentArray_push___redArg(v_extra_1385_, v___y_1382_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 2, v___x_1395_);
v___x_1397_ = v___x_1393_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_config_1383_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_extensions_1384_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_extraInj_1386_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_extraFacts_1387_);
lean_ctor_set(v_reuseFailAlloc_1399_, 5, v_symPrios_1388_);
lean_ctor_set(v_reuseFailAlloc_1399_, 6, v_norm_1389_);
lean_ctor_set(v_reuseFailAlloc_1399_, 7, v_normProcs_1390_);
lean_ctor_set(v_reuseFailAlloc_1399_, 8, v_anchorRefs_x3f_1391_);
v___x_1397_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
}
v___jp_1401_:
{
if (v_warn_1375_ == 0)
{
lean_dec(v_declName_1371_);
v___y_1382_ = v_thm_1402_;
goto v___jp_1381_;
}
else
{
lean_object* v_extensions_1407_; lean_object* v_patterns_1408_; lean_object* v_origin_1409_; lean_object* v_cnstrs_1410_; uint8_t v___x_1411_; 
v_extensions_1407_ = lean_ctor_get(v_params_1369_, 1);
v_patterns_1408_ = lean_ctor_get(v_thm_1402_, 3);
v_origin_1409_ = lean_ctor_get(v_thm_1402_, 5);
v_cnstrs_1410_ = lean_ctor_get(v_thm_1402_, 7);
v___x_1411_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1407_, v_origin_1409_, v_patterns_1408_, v_cnstrs_1410_);
if (v___x_1411_ == 0)
{
lean_dec(v_declName_1371_);
v___y_1382_ = v_thm_1402_;
goto v___jp_1381_;
}
else
{
lean_object* v___x_1412_; 
v___x_1412_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1407_, v_declName_1371_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_dec_ref_known(v___x_1412_, 1);
v___y_1382_ = v_thm_1402_;
goto v___jp_1381_;
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_thm_1402_);
lean_dec_ref(v_params_1369_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
}
v___jp_1421_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1433_ = l_Lean_PersistentArray_push___redArg(v___y_1431_, v___y_1424_);
v___x_1434_ = l_Lean_PersistentArray_push___redArg(v___x_1433_, v___y_1426_);
v___x_1435_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1435_, 0, v___y_1425_);
lean_ctor_set(v___x_1435_, 1, v___y_1430_);
lean_ctor_set(v___x_1435_, 2, v___x_1434_);
lean_ctor_set(v___x_1435_, 3, v___y_1432_);
lean_ctor_set(v___x_1435_, 4, v___y_1429_);
lean_ctor_set(v___x_1435_, 5, v___y_1422_);
lean_ctor_set(v___x_1435_, 6, v___y_1427_);
lean_ctor_set(v___x_1435_, 7, v___y_1428_);
lean_ctor_set(v___x_1435_, 8, v___y_1423_);
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
v___jp_1438_:
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1373_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v___x_1444_; 
lean_dec_ref_known(v___x_1443_, 1);
lean_inc(v_declName_1371_);
v___x_1444_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1371_, v___x_1437_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1477_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1477_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1477_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
if (lean_obj_tag(v_a_1445_) == 1)
{
lean_object* v_val_1449_; lean_object* v_config_1450_; lean_object* v_extensions_1451_; lean_object* v_extra_1452_; lean_object* v_extraInj_1453_; lean_object* v_extraFacts_1454_; lean_object* v_symPrios_1455_; lean_object* v_norm_1456_; lean_object* v_normProcs_1457_; lean_object* v_anchorRefs_x3f_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_declName_1371_);
v_val_1449_ = lean_ctor_get(v_a_1445_, 0);
lean_inc(v_val_1449_);
lean_dec_ref_known(v_a_1445_, 1);
v_config_1450_ = lean_ctor_get(v_params_1369_, 0);
v_extensions_1451_ = lean_ctor_get(v_params_1369_, 1);
v_extra_1452_ = lean_ctor_get(v_params_1369_, 2);
v_extraInj_1453_ = lean_ctor_get(v_params_1369_, 3);
v_extraFacts_1454_ = lean_ctor_get(v_params_1369_, 4);
v_symPrios_1455_ = lean_ctor_get(v_params_1369_, 5);
v_norm_1456_ = lean_ctor_get(v_params_1369_, 6);
v_normProcs_1457_ = lean_ctor_get(v_params_1369_, 7);
v_anchorRefs_x3f_1458_ = lean_ctor_get(v_params_1369_, 8);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_params_1369_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1460_ = v_params_1369_;
v_isShared_1461_ = v_isSharedCheck_1470_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_anchorRefs_x3f_1458_);
lean_inc(v_normProcs_1457_);
lean_inc(v_norm_1456_);
lean_inc(v_symPrios_1455_);
lean_inc(v_extraFacts_1454_);
lean_inc(v_extraInj_1453_);
lean_inc(v_extra_1452_);
lean_inc(v_extensions_1451_);
lean_inc(v_config_1450_);
lean_dec(v_params_1369_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1470_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1462_ = l_Lean_Array_toPArray_x27___redArg(v_val_1449_);
lean_dec(v_val_1449_);
v___x_1463_ = l_Lean_PersistentArray_append___redArg(v_extra_1452_, v___x_1462_);
lean_dec_ref(v___x_1462_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 2, v___x_1463_);
v___x_1465_ = v___x_1460_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_config_1450_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_extensions_1451_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_extraInj_1453_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_extraFacts_1454_);
lean_ctor_set(v_reuseFailAlloc_1469_, 5, v_symPrios_1455_);
lean_ctor_set(v_reuseFailAlloc_1469_, 6, v_norm_1456_);
lean_ctor_set(v_reuseFailAlloc_1469_, 7, v_normProcs_1457_);
lean_ctor_set(v_reuseFailAlloc_1469_, 8, v_anchorRefs_x3f_1458_);
v___x_1465_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1467_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1465_);
v___x_1467_ = v___x_1447_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_del_object(v___x_1447_);
lean_dec(v_a_1445_);
lean_dec_ref(v_params_1369_);
v___x_1471_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1472_ = l_Lean_MessageData_ofConstName(v_declName_1371_, v___x_1437_);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1473_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1475_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1476_;
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_declName_1371_);
lean_dec_ref(v_params_1369_);
v_a_1478_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1444_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1444_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v_declName_1371_);
lean_dec_ref(v_params_1369_);
v_a_1486_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1443_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1443_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
v___jp_1494_:
{
uint8_t v___x_1499_; 
v___x_1499_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1372_);
if (v___x_1499_ == 0)
{
uint8_t v___x_1500_; 
v___x_1500_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1372_);
lean_dec(v_kind_1372_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec_ref(v_params_1369_);
v___x_1501_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1502_ = l_Lean_MessageData_ofConstName(v_declName_1371_, v___x_1437_);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1505_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
else
{
v___y_1439_ = v___y_1495_;
v___y_1440_ = v___y_1496_;
v___y_1441_ = v___y_1497_;
v___y_1442_ = v___y_1498_;
goto v___jp_1438_;
}
}
else
{
lean_dec(v_kind_1372_);
v___y_1439_ = v___y_1495_;
v___y_1440_ = v___y_1496_;
v___y_1441_ = v___y_1497_;
v___y_1442_ = v___y_1498_;
goto v___jp_1438_;
}
}
v___jp_1515_:
{
lean_object* v_symPrios_1520_; lean_object* v___x_1521_; 
v_symPrios_1520_ = lean_ctor_get(v_params_1369_, 5);
lean_inc_ref(v_symPrios_1520_);
lean_inc(v_declName_1371_);
v___x_1521_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1371_, v_kind_1372_, v_symPrios_1520_, v___x_1437_, v_minIndexable_1373_, v___y_1519_, v___y_1518_, v___y_1517_, v___y_1516_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v_thm_1402_ = v_a_1522_;
v___y_1403_ = v___y_1519_;
v___y_1404_ = v___y_1518_;
v___y_1405_ = v___y_1517_;
v___y_1406_ = v___y_1516_;
goto v___jp_1401_;
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v_declName_1371_);
lean_dec_ref(v_params_1369_);
v_a_1523_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1521_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1521_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
v___jp_1531_:
{
if (v_suggest_1374_ == 0)
{
lean_dec(v_id_1370_);
v___y_1516_ = v___y_1535_;
v___y_1517_ = v___y_1534_;
v___y_1518_ = v___y_1533_;
v___y_1519_ = v___y_1532_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1536_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1534_);
v___x_1537_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1538_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_1536_, v___x_1537_);
lean_dec_ref(v___x_1536_);
if (v___x_1538_ == 0)
{
lean_object* v_symPrios_1539_; lean_object* v___x_1540_; 
lean_dec(v_kind_1372_);
v_symPrios_1539_ = lean_ctor_get(v_params_1369_, 5);
lean_inc_ref(v_symPrios_1539_);
lean_inc(v_declName_1371_);
v___x_1540_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1370_, v_declName_1371_, v_symPrios_1539_, v_minIndexable_1373_, v_suggest_1374_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v_thm_1402_ = v_a_1541_;
v___y_1403_ = v___y_1532_;
v___y_1404_ = v___y_1533_;
v___y_1405_ = v___y_1534_;
v___y_1406_ = v___y_1535_;
goto v___jp_1401_;
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec(v_declName_1371_);
lean_dec_ref(v_params_1369_);
v_a_1542_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1540_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1540_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_dec(v_id_1370_);
v___y_1516_ = v___y_1535_;
v___y_1517_ = v___y_1534_;
v___y_1518_ = v___y_1533_;
v___y_1519_ = v___y_1532_;
goto v___jp_1515_;
}
}
}
v___jp_1550_:
{
lean_object* v___x_1555_; 
v___x_1555_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1373_, v___y_1553_, v___y_1552_, v___y_1551_, v___y_1554_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_dec_ref_known(v___x_1555_, 1);
v___y_1532_ = v___y_1553_;
v___y_1533_ = v___y_1552_;
v___y_1534_ = v___y_1551_;
v___y_1535_ = v___y_1554_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_kind_1372_);
lean_dec(v_declName_1371_);
lean_dec(v_id_1370_);
lean_dec_ref(v_params_1369_);
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
v___jp_1564_:
{
if (lean_obj_tag(v_kind_1372_) == 2)
{
uint8_t v_gen_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v_id_1370_);
v_gen_1569_ = lean_ctor_get_uint8(v_kind_1372_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_kind_1372_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1571_ = v_kind_1372_;
v_isShared_1572_ = v_isSharedCheck_1633_;
goto v_resetjp_1570_;
}
else
{
lean_dec(v_kind_1372_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1633_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; 
v___x_1573_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1373_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_config_1574_; lean_object* v_extensions_1575_; lean_object* v_extra_1576_; lean_object* v_extraInj_1577_; lean_object* v_extraFacts_1578_; lean_object* v_symPrios_1579_; lean_object* v_norm_1580_; lean_object* v_normProcs_1581_; lean_object* v_anchorRefs_x3f_1582_; lean_object* v___x_1584_; 
lean_dec_ref_known(v___x_1573_, 1);
v_config_1574_ = lean_ctor_get(v_params_1369_, 0);
lean_inc_ref(v_config_1574_);
v_extensions_1575_ = lean_ctor_get(v_params_1369_, 1);
lean_inc_ref(v_extensions_1575_);
v_extra_1576_ = lean_ctor_get(v_params_1369_, 2);
lean_inc_ref(v_extra_1576_);
v_extraInj_1577_ = lean_ctor_get(v_params_1369_, 3);
lean_inc_ref(v_extraInj_1577_);
v_extraFacts_1578_ = lean_ctor_get(v_params_1369_, 4);
lean_inc_ref(v_extraFacts_1578_);
v_symPrios_1579_ = lean_ctor_get(v_params_1369_, 5);
lean_inc_ref(v_symPrios_1579_);
v_norm_1580_ = lean_ctor_get(v_params_1369_, 6);
lean_inc_ref(v_norm_1580_);
v_normProcs_1581_ = lean_ctor_get(v_params_1369_, 7);
lean_inc_ref(v_normProcs_1581_);
v_anchorRefs_x3f_1582_ = lean_ctor_get(v_params_1369_, 8);
lean_inc(v_anchorRefs_x3f_1582_);
lean_dec_ref(v_params_1369_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 0);
v___x_1584_ = v___x_1571_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1624_, 0, v_gen_1569_);
v___x_1584_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1585_; 
lean_inc_ref(v_symPrios_1579_);
lean_inc(v_declName_1371_);
v___x_1585_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1371_, v___x_1584_, v_symPrios_1579_, v___x_1437_, v___x_1437_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1587_, 0, v_gen_1569_);
lean_inc_ref(v_symPrios_1579_);
lean_inc(v_declName_1371_);
v___x_1588_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1371_, v___x_1587_, v_symPrios_1579_, v___x_1437_, v___x_1437_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1588_) == 0)
{
if (v_warn_1375_ == 0)
{
lean_object* v_a_1589_; 
lean_dec(v_declName_1371_);
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1588_, 1);
v___y_1422_ = v_symPrios_1579_;
v___y_1423_ = v_anchorRefs_x3f_1582_;
v___y_1424_ = v_a_1586_;
v___y_1425_ = v_config_1574_;
v___y_1426_ = v_a_1589_;
v___y_1427_ = v_norm_1580_;
v___y_1428_ = v_normProcs_1581_;
v___y_1429_ = v_extraFacts_1578_;
v___y_1430_ = v_extensions_1575_;
v___y_1431_ = v_extra_1576_;
v___y_1432_ = v_extraInj_1577_;
goto v___jp_1421_;
}
else
{
lean_object* v_a_1590_; lean_object* v_patterns_1591_; lean_object* v_origin_1592_; lean_object* v_cnstrs_1593_; uint8_t v___x_1594_; 
v_a_1590_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1588_, 1);
v_patterns_1591_ = lean_ctor_get(v_a_1586_, 3);
v_origin_1592_ = lean_ctor_get(v_a_1586_, 5);
v_cnstrs_1593_ = lean_ctor_get(v_a_1586_, 7);
v___x_1594_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1575_, v_origin_1592_, v_patterns_1591_, v_cnstrs_1593_);
if (v___x_1594_ == 0)
{
lean_dec(v_declName_1371_);
v___y_1422_ = v_symPrios_1579_;
v___y_1423_ = v_anchorRefs_x3f_1582_;
v___y_1424_ = v_a_1586_;
v___y_1425_ = v_config_1574_;
v___y_1426_ = v_a_1590_;
v___y_1427_ = v_norm_1580_;
v___y_1428_ = v_normProcs_1581_;
v___y_1429_ = v_extraFacts_1578_;
v___y_1430_ = v_extensions_1575_;
v___y_1431_ = v_extra_1576_;
v___y_1432_ = v_extraInj_1577_;
goto v___jp_1421_;
}
else
{
lean_object* v_patterns_1595_; lean_object* v_origin_1596_; lean_object* v_cnstrs_1597_; uint8_t v___x_1598_; 
v_patterns_1595_ = lean_ctor_get(v_a_1590_, 3);
v_origin_1596_ = lean_ctor_get(v_a_1590_, 5);
v_cnstrs_1597_ = lean_ctor_get(v_a_1590_, 7);
v___x_1598_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1575_, v_origin_1596_, v_patterns_1595_, v_cnstrs_1597_);
if (v___x_1598_ == 0)
{
lean_dec(v_declName_1371_);
v___y_1422_ = v_symPrios_1579_;
v___y_1423_ = v_anchorRefs_x3f_1582_;
v___y_1424_ = v_a_1586_;
v___y_1425_ = v_config_1574_;
v___y_1426_ = v_a_1590_;
v___y_1427_ = v_norm_1580_;
v___y_1428_ = v_normProcs_1581_;
v___y_1429_ = v_extraFacts_1578_;
v___y_1430_ = v_extensions_1575_;
v___y_1431_ = v_extra_1576_;
v___y_1432_ = v_extraInj_1577_;
goto v___jp_1421_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1575_, v_declName_1371_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_dec_ref_known(v___x_1599_, 1);
v___y_1422_ = v_symPrios_1579_;
v___y_1423_ = v_anchorRefs_x3f_1582_;
v___y_1424_ = v_a_1586_;
v___y_1425_ = v_config_1574_;
v___y_1426_ = v_a_1590_;
v___y_1427_ = v_norm_1580_;
v___y_1428_ = v_normProcs_1581_;
v___y_1429_ = v_extraFacts_1578_;
v___y_1430_ = v_extensions_1575_;
v___y_1431_ = v_extra_1576_;
v___y_1432_ = v_extraInj_1577_;
goto v___jp_1421_;
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1586_);
lean_dec(v_anchorRefs_x3f_1582_);
lean_dec_ref(v_normProcs_1581_);
lean_dec_ref(v_norm_1580_);
lean_dec_ref(v_symPrios_1579_);
lean_dec_ref(v_extraFacts_1578_);
lean_dec_ref(v_extraInj_1577_);
lean_dec_ref(v_extra_1576_);
lean_dec_ref(v_extensions_1575_);
lean_dec_ref(v_config_1574_);
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_a_1586_);
lean_dec(v_anchorRefs_x3f_1582_);
lean_dec_ref(v_normProcs_1581_);
lean_dec_ref(v_norm_1580_);
lean_dec_ref(v_symPrios_1579_);
lean_dec_ref(v_extraFacts_1578_);
lean_dec_ref(v_extraInj_1577_);
lean_dec_ref(v_extra_1576_);
lean_dec_ref(v_extensions_1575_);
lean_dec_ref(v_config_1574_);
lean_dec(v_declName_1371_);
v_a_1608_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1588_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1588_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_anchorRefs_x3f_1582_);
lean_dec_ref(v_normProcs_1581_);
lean_dec_ref(v_norm_1580_);
lean_dec_ref(v_symPrios_1579_);
lean_dec_ref(v_extraFacts_1578_);
lean_dec_ref(v_extraInj_1577_);
lean_dec_ref(v_extra_1576_);
lean_dec_ref(v_extensions_1575_);
lean_dec_ref(v_config_1574_);
lean_dec(v_declName_1371_);
v_a_1616_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1585_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1585_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_del_object(v___x_1571_);
lean_dec(v_declName_1371_);
lean_dec_ref(v_params_1369_);
v_a_1625_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1573_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1573_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
else
{
switch(lean_obj_tag(v_kind_1372_))
{
case 0:
{
v___y_1551_ = v___y_1567_;
v___y_1552_ = v___y_1566_;
v___y_1553_ = v___y_1565_;
v___y_1554_ = v___y_1568_;
goto v___jp_1550_;
}
case 1:
{
v___y_1551_ = v___y_1567_;
v___y_1552_ = v___y_1566_;
v___y_1553_ = v___y_1565_;
v___y_1554_ = v___y_1568_;
goto v___jp_1550_;
}
default: 
{
v___y_1532_ = v___y_1565_;
v___y_1533_ = v___y_1566_;
v___y_1534_ = v___y_1567_;
v___y_1535_ = v___y_1568_;
goto v___jp_1531_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* v_params_1676_, lean_object* v_id_1677_, lean_object* v_declName_1678_, lean_object* v_kind_1679_, lean_object* v_minIndexable_1680_, lean_object* v_suggest_1681_, lean_object* v_warn_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
uint8_t v_minIndexable_boxed_1688_; uint8_t v_suggest_boxed_1689_; uint8_t v_warn_boxed_1690_; lean_object* v_res_1691_; 
v_minIndexable_boxed_1688_ = lean_unbox(v_minIndexable_1680_);
v_suggest_boxed_1689_ = lean_unbox(v_suggest_1681_);
v_warn_boxed_1690_ = lean_unbox(v_warn_1682_);
v_res_1691_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1676_, v_id_1677_, v_declName_1678_, v_kind_1679_, v_minIndexable_boxed_1688_, v_suggest_boxed_1689_, v_warn_boxed_1690_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* v_declName_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1692_, v___y_1696_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* v_declName_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1706_, lean_object* v_constName_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1714_, lean_object* v_constName_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(v_00_u03b1_1714_, v_constName_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1722_, lean_object* v_ref_1723_, lean_object* v_constName_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1723_, v_constName_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1731_, lean_object* v_ref_1732_, lean_object* v_constName_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1731_, v_ref_1732_, v_constName_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v_ref_1732_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1740_, lean_object* v_ref_1741_, lean_object* v_msg_1742_, lean_object* v_declHint_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1741_, v_msg_1742_, v_declHint_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1750_, lean_object* v_ref_1751_, lean_object* v_msg_1752_, lean_object* v_declHint_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1750_, v_ref_1751_, v_msg_1752_, v_declHint_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v_ref_1751_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1760_, lean_object* v_declHint_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1760_, v_declHint_1761_, v___y_1765_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1768_, lean_object* v_declHint_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1768_, v_declHint_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1776_, lean_object* v_ref_1777_, lean_object* v_msg_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1777_, v_msg_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1785_, lean_object* v_ref_1786_, lean_object* v_msg_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1785_, v_ref_1786_, v_msg_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v_ref_1786_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1796_, lean_object* v_val_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_config_1801_; lean_object* v_extensions_1802_; lean_object* v_extra_1803_; lean_object* v_extraInj_1804_; lean_object* v_extraFacts_1805_; lean_object* v_symPrios_1806_; lean_object* v_norm_1807_; lean_object* v_normProcs_1808_; lean_object* v_anchorRefs_x3f_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1839_; 
v_config_1801_ = lean_ctor_get(v_params_1796_, 0);
v_extensions_1802_ = lean_ctor_get(v_params_1796_, 1);
v_extra_1803_ = lean_ctor_get(v_params_1796_, 2);
v_extraInj_1804_ = lean_ctor_get(v_params_1796_, 3);
v_extraFacts_1805_ = lean_ctor_get(v_params_1796_, 4);
v_symPrios_1806_ = lean_ctor_get(v_params_1796_, 5);
v_norm_1807_ = lean_ctor_get(v_params_1796_, 6);
v_normProcs_1808_ = lean_ctor_get(v_params_1796_, 7);
v_anchorRefs_x3f_1809_ = lean_ctor_get(v_params_1796_, 8);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_params_1796_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1811_ = v_params_1796_;
v_isShared_1812_ = v_isSharedCheck_1839_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_anchorRefs_x3f_1809_);
lean_inc(v_normProcs_1808_);
lean_inc(v_norm_1807_);
lean_inc(v_symPrios_1806_);
lean_inc(v_extraFacts_1805_);
lean_inc(v_extraInj_1804_);
lean_inc(v_extra_1803_);
lean_inc(v_extensions_1802_);
lean_inc(v_config_1801_);
lean_dec(v_params_1796_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1839_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___y_1814_; 
if (lean_obj_tag(v_anchorRefs_x3f_1809_) == 0)
{
lean_object* v___x_1837_; 
v___x_1837_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1814_ = v___x_1837_;
goto v___jp_1813_;
}
else
{
lean_object* v_val_1838_; 
v_val_1838_ = lean_ctor_get(v_anchorRefs_x3f_1809_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v_anchorRefs_x3f_1809_, 1);
v___y_1814_ = v_val_1838_;
goto v___jp_1813_;
}
v___jp_1813_:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1828_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1828_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1828_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1820_ = lean_array_push(v___y_1814_, v_a_1816_);
v___x_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 8, v___x_1821_);
v___x_1823_ = v___x_1811_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_config_1801_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_extensions_1802_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_extra_1803_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_extraInj_1804_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_extraFacts_1805_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v_symPrios_1806_);
lean_ctor_set(v_reuseFailAlloc_1827_, 6, v_norm_1807_);
lean_ctor_set(v_reuseFailAlloc_1827_, 7, v_normProcs_1808_);
lean_ctor_set(v_reuseFailAlloc_1827_, 8, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1825_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1823_);
v___x_1825_ = v___x_1818_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v___y_1814_);
lean_del_object(v___x_1811_);
lean_dec_ref(v_normProcs_1808_);
lean_dec_ref(v_norm_1807_);
lean_dec_ref(v_symPrios_1806_);
lean_dec_ref(v_extraFacts_1805_);
lean_dec_ref(v_extraInj_1804_);
lean_dec_ref(v_extra_1803_);
lean_dec_ref(v_extensions_1802_);
lean_dec_ref(v_config_1801_);
v_a_1829_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1815_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1815_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_1840_, lean_object* v_val_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1840_, v_val_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_val_1841_);
return v_res_1845_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_1848_ = l_Lean_stringToMessageData(v___x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_config_1853_; uint8_t v_revert_1854_; 
v_config_1853_ = lean_ctor_get(v_params_1849_, 0);
v_revert_1854_ = lean_ctor_get_uint8(v_config_1853_, sizeof(void*)*14 + 30);
if (v_revert_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_1858_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1857_, v_a_1850_, v_a_1851_);
return v___x_1858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec_ref(v_params_1859_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_1864_, lean_object* v___y_1865_){
_start:
{
uint8_t v___x_1867_; 
v___x_1867_ = l_Lean_Expr_hasMVar(v_e_1864_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_e_1864_);
return v___x_1868_;
}
else
{
lean_object* v___x_1869_; lean_object* v_mctx_1870_; lean_object* v___x_1871_; lean_object* v_fst_1872_; lean_object* v_snd_1873_; lean_object* v___x_1874_; lean_object* v_cache_1875_; lean_object* v_zetaDeltaFVarIds_1876_; lean_object* v_postponed_1877_; lean_object* v_diag_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1887_; 
v___x_1869_ = lean_st_ref_get(v___y_1865_);
v_mctx_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc_ref(v_mctx_1870_);
lean_dec(v___x_1869_);
v___x_1871_ = l_Lean_instantiateMVarsCore(v_mctx_1870_, v_e_1864_);
v_fst_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_fst_1872_);
v_snd_1873_ = lean_ctor_get(v___x_1871_, 1);
lean_inc(v_snd_1873_);
lean_dec_ref(v___x_1871_);
v___x_1874_ = lean_st_ref_take(v___y_1865_);
v_cache_1875_ = lean_ctor_get(v___x_1874_, 1);
v_zetaDeltaFVarIds_1876_ = lean_ctor_get(v___x_1874_, 2);
v_postponed_1877_ = lean_ctor_get(v___x_1874_, 3);
v_diag_1878_ = lean_ctor_get(v___x_1874_, 4);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v___x_1874_, 0);
lean_dec(v_unused_1888_);
v___x_1880_ = v___x_1874_;
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_diag_1878_);
lean_inc(v_postponed_1877_);
lean_inc(v_zetaDeltaFVarIds_1876_);
lean_inc(v_cache_1875_);
lean_dec(v___x_1874_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v_snd_1873_);
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_snd_1873_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_cache_1875_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v_zetaDeltaFVarIds_1876_);
lean_ctor_set(v_reuseFailAlloc_1886_, 3, v_postponed_1877_);
lean_ctor_set(v_reuseFailAlloc_1886_, 4, v_diag_1878_);
v___x_1883_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_st_ref_put(v___y_1865_, v___x_1883_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v_fst_1872_);
return v___x_1885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1889_, v___y_1890_);
lean_dec(v___y_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1893_, v___y_1897_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(lean_object* v_p_1913_, lean_object* v_term_1914_, lean_object* v___x_1915_, uint8_t v___x_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_toCold_1924_; lean_object* v_currRecDepth_1925_; lean_object* v_ref_1926_; uint16_t v_optionFlags_1927_; uint8_t v_suppressElabErrors_1928_; uint8_t v_isRecordingDeps_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1997_; 
v_toCold_1924_ = lean_ctor_get(v___y_1921_, 0);
v_currRecDepth_1925_ = lean_ctor_get(v___y_1921_, 1);
v_ref_1926_ = lean_ctor_get(v___y_1921_, 2);
v_optionFlags_1927_ = lean_ctor_get_uint16(v___y_1921_, sizeof(void*)*3);
v_suppressElabErrors_1928_ = lean_ctor_get_uint8(v___y_1921_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1929_ = lean_ctor_get_uint8(v___y_1921_, sizeof(void*)*3 + 3);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___y_1921_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1931_ = v___y_1921_;
v_isShared_1932_ = v_isSharedCheck_1997_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_ref_1926_);
lean_inc(v_currRecDepth_1925_);
lean_inc(v_toCold_1924_);
lean_dec(v___y_1921_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1997_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v_ref_1933_; lean_object* v___x_1935_; 
v_ref_1933_ = l_Lean_replaceRef(v_p_1913_, v_ref_1926_);
lean_dec(v_ref_1926_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 2, v_ref_1933_);
v___x_1935_ = v___x_1931_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_toCold_1924_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_currRecDepth_1925_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_ref_1933_);
lean_ctor_set_uint16(v_reuseFailAlloc_1996_, sizeof(void*)*3, v_optionFlags_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1996_, sizeof(void*)*3 + 2, v_suppressElabErrors_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1996_, sizeof(void*)*3 + 3, v_isRecordingDeps_1929_);
v___x_1935_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_Elab_Term_elabTerm(v_term_1914_, v___x_1915_, v___x_1916_, v___x_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___x_1935_, v___y_1922_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = 1;
v___x_1939_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1938_, v___x_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___x_1935_, v___y_1922_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v___x_1940_; lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref_known(v___x_1939_, 1);
v___x_1940_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_1937_, v___y_1920_);
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1979_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1979_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
uint8_t v___x_1945_; 
v___x_1945_ = l_Lean_Expr_hasSyntheticSorry(v_a_1941_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = l_Lean_Expr_eta(v_a_1941_);
v___x_1947_ = l_Lean_Expr_hasMVar(v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
lean_dec_ref(v___x_1935_);
v___x_1948_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0));
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v___x_1946_);
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1950_);
v___x_1952_ = v___x_1943_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
else
{
lean_object* v___x_1954_; 
lean_del_object(v___x_1943_);
v___x_1954_ = l_Lean_Meta_abstractMVars(v___x_1946_, v___x_1916_, v___y_1919_, v___y_1920_, v___x_1935_, v___y_1922_);
lean_dec_ref(v___x_1935_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1966_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1966_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1966_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v_paramNames_1959_; lean_object* v_expr_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v_paramNames_1959_ = lean_ctor_get(v_a_1955_, 0);
lean_inc_ref(v_paramNames_1959_);
v_expr_1960_ = lean_ctor_get(v_a_1955_, 2);
lean_inc_ref(v_expr_1960_);
lean_dec(v_a_1955_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v_paramNames_1959_);
lean_ctor_set(v___x_1961_, 1, v_expr_1960_);
v___x_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1962_);
v___x_1964_ = v___x_1957_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_a_1967_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1954_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1954_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_dec(v_a_1941_);
lean_dec_ref(v___x_1935_);
v___x_1975_ = lean_box(0);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1975_);
v___x_1977_ = v___x_1943_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_a_1937_);
lean_dec_ref(v___x_1935_);
v_a_1980_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1939_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1939_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v___x_1935_);
v_a_1988_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1936_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1936_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v_p_1998_, lean_object* v_term_1999_, lean_object* v___x_2000_, lean_object* v___x_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
uint8_t v___x_12212__boxed_2009_; lean_object* v_res_2010_; 
v___x_12212__boxed_2009_ = lean_unbox(v___x_2001_);
v_res_2010_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v_p_1998_, v_term_1999_, v___x_2000_, v___x_12212__boxed_2009_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v_p_1998_);
return v_res_2010_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2));
v___x_2016_ = l_Lean_stringToMessageData(v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_params_2017_, lean_object* v_p_2018_, lean_object* v_fst_2019_, lean_object* v_snd_2020_, uint8_t v___x_2021_, uint8_t v_minIndexable_2022_, lean_object* v_kind_2023_, lean_object* v_idx_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_symPrios_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; lean_object* v___x_2035_; 
v_symPrios_2030_ = lean_ctor_get(v_params_2017_, 5);
lean_inc_ref(v_symPrios_2030_);
lean_dec_ref(v_params_2017_);
v___x_2031_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1));
v___x_2032_ = lean_name_append_index_after(v___x_2031_, v_idx_2024_);
v___x_2033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v_p_2018_);
v___x_2034_ = 0;
v___x_2035_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2033_, v_fst_2019_, v_snd_2020_, v_kind_2023_, v_symPrios_2030_, v___x_2021_, v___x_2034_, v_minIndexable_2022_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2046_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2046_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2046_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
if (lean_obj_tag(v_a_2036_) == 1)
{
lean_object* v_val_2040_; lean_object* v___x_2042_; 
v_val_2040_ = lean_ctor_get(v_a_2036_, 0);
lean_inc(v_val_2040_);
lean_dec_ref_known(v_a_2036_, 1);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v_val_2040_);
v___x_2042_ = v___x_2038_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_val_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_del_object(v___x_2038_);
lean_dec(v_a_2036_);
v___x_2044_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3);
v___x_2045_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2044_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
return v___x_2045_;
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
v_a_2047_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2035_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2035_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_params_2055_, lean_object* v_p_2056_, lean_object* v_fst_2057_, lean_object* v_snd_2058_, lean_object* v___x_2059_, lean_object* v_minIndexable_2060_, lean_object* v_kind_2061_, lean_object* v_idx_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
uint8_t v___x_12386__boxed_2068_; uint8_t v_minIndexable_boxed_2069_; lean_object* v_res_2070_; 
v___x_12386__boxed_2068_ = lean_unbox(v___x_2059_);
v_minIndexable_boxed_2069_ = lean_unbox(v_minIndexable_2060_);
v_res_2070_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_params_2055_, v_p_2056_, v_fst_2057_, v_snd_2058_, v___x_12386__boxed_2068_, v_minIndexable_boxed_2069_, v_kind_2061_, v_idx_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2070_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = lean_box(1);
v___x_2072_ = l_Lean_MessageData_ofFormat(v___x_2071_);
return v___x_2072_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2));
v___x_2077_ = l_Lean_MessageData_ofFormat(v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(lean_object* v_x_2078_, lean_object* v_x_2079_){
_start:
{
if (lean_obj_tag(v_x_2079_) == 0)
{
return v_x_2078_;
}
else
{
lean_object* v_head_2080_; lean_object* v_tail_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2103_; 
v_head_2080_ = lean_ctor_get(v_x_2079_, 0);
v_tail_2081_ = lean_ctor_get(v_x_2079_, 1);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_x_2079_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2083_ = v_x_2079_;
v_isShared_2084_ = v_isSharedCheck_2103_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_tail_2081_);
lean_inc(v_head_2080_);
lean_dec(v_x_2079_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2103_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_before_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2101_; 
v_before_2085_ = lean_ctor_get(v_head_2080_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_head_2080_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; 
v_unused_2102_ = lean_ctor_get(v_head_2080_, 1);
lean_dec(v_unused_2102_);
v___x_2087_ = v_head_2080_;
v_isShared_2088_ = v_isSharedCheck_2101_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_before_2085_);
lean_dec(v_head_2080_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2101_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 7);
lean_ctor_set(v___x_2087_, 1, v___x_2089_);
lean_ctor_set(v___x_2087_, 0, v_x_2078_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_x_2078_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2092_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3);
if (v_isShared_2084_ == 0)
{
lean_ctor_set_tag(v___x_2083_, 7);
lean_ctor_set(v___x_2083_, 1, v___x_2092_);
lean_ctor_set(v___x_2083_, 0, v___x_2091_);
v___x_2094_ = v___x_2083_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = l_Lean_MessageData_ofSyntax(v_before_2085_);
v___x_2096_ = l_Lean_indentD(v___x_2095_);
v___x_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2094_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v_x_2078_ = v___x_2097_;
v_x_2079_ = v_tail_2081_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1));
v___x_2108_ = l_Lean_MessageData_ofFormat(v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(lean_object* v_msgData_2109_, lean_object* v_macroStack_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2113_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2111_);
v___x_2114_ = l_Lean_Elab_pp_macroStack;
v___x_2115_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_2113_, v___x_2114_);
lean_dec_ref(v___x_2113_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; 
lean_dec(v_macroStack_2110_);
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v_msgData_2109_);
return v___x_2116_;
}
else
{
if (lean_obj_tag(v_macroStack_2110_) == 0)
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v_msgData_2109_);
return v___x_2117_;
}
else
{
lean_object* v_head_2118_; lean_object* v_after_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2134_; 
v_head_2118_ = lean_ctor_get(v_macroStack_2110_, 0);
lean_inc(v_head_2118_);
v_after_2119_ = lean_ctor_get(v_head_2118_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_head_2118_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v_head_2118_, 0);
lean_dec(v_unused_2135_);
v___x_2121_ = v_head_2118_;
v_isShared_2122_ = v_isSharedCheck_2134_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_after_2119_);
lean_dec(v_head_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2134_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2122_ == 0)
{
lean_ctor_set_tag(v___x_2121_, 7);
lean_ctor_set(v___x_2121_, 1, v___x_2123_);
lean_ctor_set(v___x_2121_, 0, v_msgData_2109_);
v___x_2125_ = v___x_2121_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_msgData_2109_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v_msgData_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2126_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = l_Lean_MessageData_ofSyntax(v_after_2119_);
v___x_2129_ = l_Lean_indentD(v___x_2128_);
v_msgData_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2130_, 0, v___x_2127_);
lean_ctor_set(v_msgData_2130_, 1, v___x_2129_);
v___x_2131_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(v_msgData_2130_, v_macroStack_2110_);
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
return v___x_2132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2136_, lean_object* v_macroStack_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2136_, v_macroStack_2137_, v___y_2138_);
lean_dec_ref(v___y_2138_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(lean_object* v_msg_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_ref_2149_; lean_object* v_macroStack_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v_a_2153_; lean_object* v___x_2154_; lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2163_; 
v_ref_2149_ = lean_ctor_get(v___y_2146_, 2);
v_macroStack_2150_ = lean_ctor_get(v___y_2142_, 1);
v___x_2151_ = l_Lean_Elab_getBetterRef(v_ref_2149_, v_macroStack_2150_);
v___x_2152_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2141_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref(v___x_2152_);
lean_inc(v_macroStack_2150_);
v___x_2154_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_a_2153_, v_macroStack_2150_, v___y_2146_);
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2157_ = v___x_2154_;
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2151_);
lean_ctor_set(v___x_2159_, 1, v_a_2155_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set_tag(v___x_2157_, 1);
lean_ctor_set(v___x_2157_, 0, v___x_2159_);
v___x_2161_ = v___x_2157_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v_msg_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
return v_res_2172_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2175_ = l_Lean_stringToMessageData(v___x_2174_);
return v___x_2175_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
return v___x_2178_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
return v___x_2181_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2187_, lean_object* v_p_2188_, lean_object* v_mod_x3f_2189_, lean_object* v_term_2190_, uint8_t v_minIndexable_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___y_2200_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v_kind_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v_toCold_2531_; lean_object* v_currRecDepth_2532_; lean_object* v_ref_2533_; uint16_t v_optionFlags_2534_; uint8_t v_suppressElabErrors_2535_; uint8_t v_isRecordingDeps_2536_; lean_object* v_ref_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_toCold_2531_ = lean_ctor_get(v_a_2196_, 0);
v_currRecDepth_2532_ = lean_ctor_get(v_a_2196_, 1);
v_ref_2533_ = lean_ctor_get(v_a_2196_, 2);
v_optionFlags_2534_ = lean_ctor_get_uint16(v_a_2196_, sizeof(void*)*3);
v_suppressElabErrors_2535_ = lean_ctor_get_uint8(v_a_2196_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2536_ = lean_ctor_get_uint8(v_a_2196_, sizeof(void*)*3 + 3);
v_ref_2537_ = l_Lean_replaceRef(v_p_2188_, v_ref_2533_);
lean_inc(v_currRecDepth_2532_);
lean_inc_ref(v_toCold_2531_);
v___x_2538_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2538_, 0, v_toCold_2531_);
lean_ctor_set(v___x_2538_, 1, v_currRecDepth_2532_);
lean_ctor_set(v___x_2538_, 2, v_ref_2537_);
lean_ctor_set_uint16(v___x_2538_, sizeof(void*)*3, v_optionFlags_2534_);
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*3 + 2, v_suppressElabErrors_2535_);
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*3 + 3, v_isRecordingDeps_2536_);
v___x_2539_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2187_, v___x_2538_, v_a_2197_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_dec_ref_known(v___x_2539_, 1);
if (lean_obj_tag(v_mod_x3f_2189_) == 1)
{
lean_object* v_val_2540_; lean_object* v___x_2541_; 
v_val_2540_ = lean_ctor_get(v_mod_x3f_2189_, 0);
lean_inc(v_val_2540_);
v___x_2541_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2540_, v___x_2538_, v_a_2197_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
switch(lean_obj_tag(v_a_2542_))
{
case 0:
{
lean_object* v_k_2543_; 
v_k_2543_ = lean_ctor_get(v_a_2542_, 0);
lean_inc(v_k_2543_);
lean_dec_ref_known(v_a_2542_, 1);
if (lean_obj_tag(v_k_2543_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2189_, 1);
lean_dec(v_term_2190_);
lean_dec(v_p_2188_);
lean_dec_ref(v_params_2187_);
v___y_2490_ = v_a_2192_;
v___y_2491_ = v_a_2193_;
v___y_2492_ = v_a_2194_;
v___y_2493_ = v_a_2195_;
v___y_2494_ = v___x_2538_;
v___y_2495_ = v_a_2197_;
goto v___jp_2489_;
}
else
{
v_kind_2424_ = v_k_2543_;
v___y_2425_ = v_a_2192_;
v___y_2426_ = v_a_2193_;
v___y_2427_ = v_a_2194_;
v___y_2428_ = v_a_2195_;
v___y_2429_ = v___x_2538_;
v___y_2430_ = v_a_2197_;
goto v___jp_2423_;
}
}
case 1:
{
lean_dec_ref_known(v_a_2542_, 0);
lean_dec_ref_known(v_mod_x3f_2189_, 1);
lean_dec(v_term_2190_);
lean_dec(v_p_2188_);
lean_dec_ref(v_params_2187_);
v___y_2507_ = v_a_2192_;
v___y_2508_ = v_a_2193_;
v___y_2509_ = v_a_2194_;
v___y_2510_ = v_a_2195_;
v___y_2511_ = v___x_2538_;
v___y_2512_ = v_a_2197_;
goto v___jp_2506_;
}
case 3:
{
v___y_2524_ = v_a_2192_;
v___y_2525_ = v_a_2193_;
v___y_2526_ = v_a_2194_;
v___y_2527_ = v_a_2195_;
v___y_2528_ = v___x_2538_;
v___y_2529_ = v_a_2197_;
goto v___jp_2523_;
}
case 5:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref_known(v_a_2542_, 1);
lean_dec_ref_known(v_mod_x3f_2189_, 1);
lean_dec(v_term_2190_);
lean_dec(v_p_2188_);
lean_dec_ref(v_params_2187_);
v___x_2544_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2545_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2544_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v___x_2538_, v_a_2197_);
lean_dec_ref_known(v___x_2538_, 3);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
case 8:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec_ref_known(v_a_2542_, 0);
lean_dec_ref_known(v_mod_x3f_2189_, 1);
lean_dec(v_term_2190_);
lean_dec(v_p_2188_);
lean_dec_ref(v_params_2187_);
v___x_2554_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2555_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2554_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v___x_2538_, v_a_2197_);
lean_dec_ref_known(v___x_2538_, 3);
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
case 10:
{
lean_dec_ref_known(v_a_2542_, 0);
lean_dec_ref_known(v_mod_x3f_2189_, 1);
lean_dec(v_term_2190_);
lean_dec(v_p_2188_);
lean_dec_ref(v_params_2187_);
v___y_2507_ = v_a_2192_;
v___y_2508_ = v_a_2193_;
v___y_2509_ = v_a_2194_;
v___y_2510_ = v_a_2195_;
v___y_2511_ = v___x_2538_;
v___y_2512_ = v_a_2197_;
goto v___jp_2506_;
}
default: 
{
lean_dec(v_a_2542_);
lean_dec_ref_known(v_mod_x3f_2189_, 1);
lean_dec(v_term_2190_);
lean_dec(v_p_2188_);
lean_dec_ref(v_params_2187_);
v___y_2490_ = v_a_2192_;
v___y_2491_ = v_a_2193_;
v___y_2492_ = v_a_2194_;
v___y_2493_ = v_a_2195_;
v___y_2494_ = v___x_2538_;
v___y_2495_ = v_a_2197_;
goto v___jp_2489_;
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec_ref_known(v_mod_x3f_2189_, 1);
lean_dec_ref_known(v___x_2538_, 3);
lean_dec(v_term_2190_);
lean_dec(v_p_2188_);
lean_dec_ref(v_params_2187_);
v_a_2564_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2541_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2541_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
v___y_2524_ = v_a_2192_;
v___y_2525_ = v_a_2193_;
v___y_2526_ = v_a_2194_;
v___y_2527_ = v_a_2195_;
v___y_2528_ = v___x_2538_;
v___y_2529_ = v_a_2197_;
goto v___jp_2523_;
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref_known(v___x_2538_, 3);
lean_dec(v_term_2190_);
lean_dec(v_mod_x3f_2189_);
lean_dec(v_p_2188_);
lean_dec_ref(v_params_2187_);
v_a_2572_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2539_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2539_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
v___jp_2199_:
{
lean_object* v_config_2201_; lean_object* v_extensions_2202_; lean_object* v_extra_2203_; lean_object* v_extraInj_2204_; lean_object* v_extraFacts_2205_; lean_object* v_symPrios_2206_; lean_object* v_norm_2207_; lean_object* v_normProcs_2208_; lean_object* v_anchorRefs_x3f_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2218_; 
v_config_2201_ = lean_ctor_get(v_params_2187_, 0);
v_extensions_2202_ = lean_ctor_get(v_params_2187_, 1);
v_extra_2203_ = lean_ctor_get(v_params_2187_, 2);
v_extraInj_2204_ = lean_ctor_get(v_params_2187_, 3);
v_extraFacts_2205_ = lean_ctor_get(v_params_2187_, 4);
v_symPrios_2206_ = lean_ctor_get(v_params_2187_, 5);
v_norm_2207_ = lean_ctor_get(v_params_2187_, 6);
v_normProcs_2208_ = lean_ctor_get(v_params_2187_, 7);
v_anchorRefs_x3f_2209_ = lean_ctor_get(v_params_2187_, 8);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_params_2187_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2211_ = v_params_2187_;
v_isShared_2212_ = v_isSharedCheck_2218_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_anchorRefs_x3f_2209_);
lean_inc(v_normProcs_2208_);
lean_inc(v_norm_2207_);
lean_inc(v_symPrios_2206_);
lean_inc(v_extraFacts_2205_);
lean_inc(v_extraInj_2204_);
lean_inc(v_extra_2203_);
lean_inc(v_extensions_2202_);
lean_inc(v_config_2201_);
lean_dec(v_params_2187_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2218_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2205_, v___y_2200_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 4, v___x_2213_);
v___x_2215_ = v___x_2211_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_config_2201_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_extensions_2202_);
lean_ctor_set(v_reuseFailAlloc_2217_, 2, v_extra_2203_);
lean_ctor_set(v_reuseFailAlloc_2217_, 3, v_extraInj_2204_);
lean_ctor_set(v_reuseFailAlloc_2217_, 4, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2217_, 5, v_symPrios_2206_);
lean_ctor_set(v_reuseFailAlloc_2217_, 6, v_norm_2207_);
lean_ctor_set(v_reuseFailAlloc_2217_, 7, v_normProcs_2208_);
lean_ctor_set(v_reuseFailAlloc_2217_, 8, v_anchorRefs_x3f_2209_);
v___x_2215_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2216_; 
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
}
v___jp_2219_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2229_ = lean_array_get_size(v___y_2220_);
lean_dec_ref(v___y_2220_);
v___x_2230_ = lean_unsigned_to_nat(0u);
v___x_2231_ = lean_nat_dec_eq(v___x_2229_, v___x_2230_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref(v___y_2222_);
lean_dec_ref(v_params_2187_);
v___x_2232_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2233_ = l_Lean_indentExpr(v___y_2221_);
v___x_2234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2232_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2234_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec_ref(v___y_2227_);
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
lean_dec_ref(v___y_2227_);
lean_dec_ref(v___y_2221_);
v___y_2200_ = v___y_2222_;
goto v___jp_2199_;
}
}
v___jp_2244_:
{
lean_object* v___x_2261_; 
lean_inc(v___y_2260_);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
v___x_2261_ = lean_apply_7(v___y_2256_, v___y_2255_, v___y_2251_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, lean_box(0));
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2271_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2271_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2271_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2266_ = l_Lean_PersistentArray_push___redArg(v___y_2254_, v_a_2262_);
v___x_2267_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2267_, 0, v___y_2246_);
lean_ctor_set(v___x_2267_, 1, v___y_2252_);
lean_ctor_set(v___x_2267_, 2, v___x_2266_);
lean_ctor_set(v___x_2267_, 3, v___y_2250_);
lean_ctor_set(v___x_2267_, 4, v___y_2245_);
lean_ctor_set(v___x_2267_, 5, v___y_2253_);
lean_ctor_set(v___x_2267_, 6, v___y_2249_);
lean_ctor_set(v___x_2267_, 7, v___y_2247_);
lean_ctor_set(v___x_2267_, 8, v___y_2248_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2267_);
v___x_2269_ = v___x_2264_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec_ref(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec_ref(v___y_2245_);
v_a_2272_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2261_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2261_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
v___jp_2280_:
{
lean_object* v___x_2297_; 
v___x_2297_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2191_, v___y_2296_, v___y_2294_, v___y_2286_, v___y_2293_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_dec_ref_known(v___x_2297_, 1);
v___y_2245_ = v___y_2287_;
v___y_2246_ = v___y_2288_;
v___y_2247_ = v___y_2289_;
v___y_2248_ = v___y_2290_;
v___y_2249_ = v___y_2291_;
v___y_2250_ = v___y_2292_;
v___y_2251_ = v___y_2281_;
v___y_2252_ = v___y_2282_;
v___y_2253_ = v___y_2295_;
v___y_2254_ = v___y_2285_;
v___y_2255_ = v___y_2284_;
v___y_2256_ = v___y_2283_;
v___y_2257_ = v___y_2296_;
v___y_2258_ = v___y_2294_;
v___y_2259_ = v___y_2286_;
v___y_2260_ = v___y_2293_;
goto v___jp_2244_;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v___y_2295_);
lean_dec_ref(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
v___jp_2306_:
{
uint8_t v___x_2318_; 
v___x_2318_ = l_Lean_Expr_isForall(v___y_2308_);
if (v___x_2318_ == 0)
{
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
if (lean_obj_tag(v_mod_x3f_2189_) == 0)
{
v___y_2220_ = v___y_2307_;
v___y_2221_ = v___y_2308_;
v___y_2222_ = v___y_2309_;
v___y_2223_ = v___y_2312_;
v___y_2224_ = v___y_2313_;
v___y_2225_ = v___y_2314_;
v___y_2226_ = v___y_2315_;
v___y_2227_ = v___y_2316_;
v___y_2228_ = v___y_2317_;
goto v___jp_2219_;
}
else
{
lean_dec_ref_known(v_mod_x3f_2189_, 1);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v___y_2309_);
lean_dec_ref(v___y_2307_);
lean_dec_ref(v_params_2187_);
v___x_2319_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2320_ = l_Lean_indentExpr(v___y_2308_);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2321_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec_ref(v___y_2316_);
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
else
{
v___y_2220_ = v___y_2307_;
v___y_2221_ = v___y_2308_;
v___y_2222_ = v___y_2309_;
v___y_2223_ = v___y_2312_;
v___y_2224_ = v___y_2313_;
v___y_2225_ = v___y_2314_;
v___y_2226_ = v___y_2315_;
v___y_2227_ = v___y_2316_;
v___y_2228_ = v___y_2317_;
goto v___jp_2219_;
}
}
}
else
{
lean_object* v_extra_2331_; 
lean_dec_ref(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v_mod_x3f_2189_);
v_extra_2331_ = lean_ctor_get(v_params_2187_, 2);
lean_inc_ref(v_extra_2331_);
if (lean_obj_tag(v___y_2311_) == 2)
{
lean_object* v_config_2332_; lean_object* v_extensions_2333_; lean_object* v_extraInj_2334_; lean_object* v_extraFacts_2335_; lean_object* v_symPrios_2336_; lean_object* v_norm_2337_; lean_object* v_normProcs_2338_; lean_object* v_anchorRefs_x3f_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2394_; 
v_config_2332_ = lean_ctor_get(v_params_2187_, 0);
v_extensions_2333_ = lean_ctor_get(v_params_2187_, 1);
v_extraInj_2334_ = lean_ctor_get(v_params_2187_, 3);
v_extraFacts_2335_ = lean_ctor_get(v_params_2187_, 4);
v_symPrios_2336_ = lean_ctor_get(v_params_2187_, 5);
v_norm_2337_ = lean_ctor_get(v_params_2187_, 6);
v_normProcs_2338_ = lean_ctor_get(v_params_2187_, 7);
v_anchorRefs_x3f_2339_ = lean_ctor_get(v_params_2187_, 8);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_params_2187_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; 
v_unused_2395_ = lean_ctor_get(v_params_2187_, 2);
lean_dec(v_unused_2395_);
v___x_2341_ = v_params_2187_;
v_isShared_2342_ = v_isSharedCheck_2394_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_anchorRefs_x3f_2339_);
lean_inc(v_normProcs_2338_);
lean_inc(v_norm_2337_);
lean_inc(v_symPrios_2336_);
lean_inc(v_extraFacts_2335_);
lean_inc(v_extraInj_2334_);
lean_inc(v_extensions_2333_);
lean_inc(v_config_2332_);
lean_dec(v_params_2187_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2394_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v_size_2343_; uint8_t v_gen_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2393_; 
v_size_2343_ = lean_ctor_get(v_extra_2331_, 2);
v_gen_2344_ = lean_ctor_get_uint8(v___y_2311_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___y_2311_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2346_ = v___y_2311_;
v_isShared_2347_ = v_isSharedCheck_2393_;
goto v_resetjp_2345_;
}
else
{
lean_dec(v___y_2311_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2393_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; 
v___x_2348_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2191_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v___x_2350_; 
lean_dec_ref_known(v___x_2348_, 1);
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 0);
v___x_2350_ = v___x_2346_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, 0, v_gen_2344_);
v___x_2350_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; 
lean_inc_ref(v___y_2310_);
lean_inc(v___y_2317_);
lean_inc_ref(v___y_2316_);
lean_inc(v___y_2315_);
lean_inc_ref(v___y_2314_);
lean_inc(v_size_2343_);
v___x_2351_ = lean_apply_7(v___y_2310_, v___x_2350_, v_size_2343_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, lean_box(0));
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v___x_2353_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2353_, 0, v_gen_2344_);
lean_inc(v___y_2317_);
lean_inc(v___y_2315_);
lean_inc_ref(v___y_2314_);
lean_inc(v_size_2343_);
v___x_2354_ = lean_apply_7(v___y_2310_, v___x_2353_, v_size_2343_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, lean_box(0));
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2367_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2367_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2367_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2359_ = l_Lean_PersistentArray_push___redArg(v_extra_2331_, v_a_2352_);
v___x_2360_ = l_Lean_PersistentArray_push___redArg(v___x_2359_, v_a_2355_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 2, v___x_2360_);
v___x_2362_ = v___x_2341_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_config_2332_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_extensions_2333_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2366_, 3, v_extraInj_2334_);
lean_ctor_set(v_reuseFailAlloc_2366_, 4, v_extraFacts_2335_);
lean_ctor_set(v_reuseFailAlloc_2366_, 5, v_symPrios_2336_);
lean_ctor_set(v_reuseFailAlloc_2366_, 6, v_norm_2337_);
lean_ctor_set(v_reuseFailAlloc_2366_, 7, v_normProcs_2338_);
lean_ctor_set(v_reuseFailAlloc_2366_, 8, v_anchorRefs_x3f_2339_);
v___x_2362_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2364_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2362_);
v___x_2364_ = v___x_2357_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_a_2352_);
lean_del_object(v___x_2341_);
lean_dec(v_anchorRefs_x3f_2339_);
lean_dec_ref(v_normProcs_2338_);
lean_dec_ref(v_norm_2337_);
lean_dec_ref(v_symPrios_2336_);
lean_dec_ref(v_extraFacts_2335_);
lean_dec_ref(v_extraInj_2334_);
lean_dec_ref(v_extensions_2333_);
lean_dec_ref(v_config_2332_);
lean_dec_ref(v_extra_2331_);
v_a_2368_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2354_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2354_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_del_object(v___x_2341_);
lean_dec(v_anchorRefs_x3f_2339_);
lean_dec_ref(v_normProcs_2338_);
lean_dec_ref(v_norm_2337_);
lean_dec_ref(v_symPrios_2336_);
lean_dec_ref(v_extraFacts_2335_);
lean_dec_ref(v_extraInj_2334_);
lean_dec_ref(v_extensions_2333_);
lean_dec_ref(v_config_2332_);
lean_dec_ref(v_extra_2331_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v___y_2310_);
v_a_2376_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2351_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2351_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_del_object(v___x_2346_);
lean_del_object(v___x_2341_);
lean_dec(v_anchorRefs_x3f_2339_);
lean_dec_ref(v_normProcs_2338_);
lean_dec_ref(v_norm_2337_);
lean_dec_ref(v_symPrios_2336_);
lean_dec_ref(v_extraFacts_2335_);
lean_dec_ref(v_extraInj_2334_);
lean_dec_ref(v_extensions_2333_);
lean_dec_ref(v_config_2332_);
lean_dec_ref(v_extra_2331_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v___y_2310_);
v_a_2385_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2348_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2348_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
else
{
switch(lean_obj_tag(v___y_2311_))
{
case 0:
{
lean_object* v_config_2396_; lean_object* v_extensions_2397_; lean_object* v_extraInj_2398_; lean_object* v_extraFacts_2399_; lean_object* v_symPrios_2400_; lean_object* v_norm_2401_; lean_object* v_normProcs_2402_; lean_object* v_anchorRefs_x3f_2403_; lean_object* v_size_2404_; 
v_config_2396_ = lean_ctor_get(v_params_2187_, 0);
lean_inc_ref(v_config_2396_);
v_extensions_2397_ = lean_ctor_get(v_params_2187_, 1);
lean_inc_ref(v_extensions_2397_);
v_extraInj_2398_ = lean_ctor_get(v_params_2187_, 3);
lean_inc_ref(v_extraInj_2398_);
v_extraFacts_2399_ = lean_ctor_get(v_params_2187_, 4);
lean_inc_ref(v_extraFacts_2399_);
v_symPrios_2400_ = lean_ctor_get(v_params_2187_, 5);
lean_inc_ref(v_symPrios_2400_);
v_norm_2401_ = lean_ctor_get(v_params_2187_, 6);
lean_inc_ref(v_norm_2401_);
v_normProcs_2402_ = lean_ctor_get(v_params_2187_, 7);
lean_inc_ref(v_normProcs_2402_);
v_anchorRefs_x3f_2403_ = lean_ctor_get(v_params_2187_, 8);
lean_inc(v_anchorRefs_x3f_2403_);
lean_dec_ref(v_params_2187_);
v_size_2404_ = lean_ctor_get(v_extra_2331_, 2);
lean_inc(v_size_2404_);
v___y_2281_ = v_size_2404_;
v___y_2282_ = v_extensions_2397_;
v___y_2283_ = v___y_2310_;
v___y_2284_ = v___y_2311_;
v___y_2285_ = v_extra_2331_;
v___y_2286_ = v___y_2316_;
v___y_2287_ = v_extraFacts_2399_;
v___y_2288_ = v_config_2396_;
v___y_2289_ = v_normProcs_2402_;
v___y_2290_ = v_anchorRefs_x3f_2403_;
v___y_2291_ = v_norm_2401_;
v___y_2292_ = v_extraInj_2398_;
v___y_2293_ = v___y_2317_;
v___y_2294_ = v___y_2315_;
v___y_2295_ = v_symPrios_2400_;
v___y_2296_ = v___y_2314_;
goto v___jp_2280_;
}
case 1:
{
lean_object* v_config_2405_; lean_object* v_extensions_2406_; lean_object* v_extraInj_2407_; lean_object* v_extraFacts_2408_; lean_object* v_symPrios_2409_; lean_object* v_norm_2410_; lean_object* v_normProcs_2411_; lean_object* v_anchorRefs_x3f_2412_; lean_object* v_size_2413_; 
v_config_2405_ = lean_ctor_get(v_params_2187_, 0);
lean_inc_ref(v_config_2405_);
v_extensions_2406_ = lean_ctor_get(v_params_2187_, 1);
lean_inc_ref(v_extensions_2406_);
v_extraInj_2407_ = lean_ctor_get(v_params_2187_, 3);
lean_inc_ref(v_extraInj_2407_);
v_extraFacts_2408_ = lean_ctor_get(v_params_2187_, 4);
lean_inc_ref(v_extraFacts_2408_);
v_symPrios_2409_ = lean_ctor_get(v_params_2187_, 5);
lean_inc_ref(v_symPrios_2409_);
v_norm_2410_ = lean_ctor_get(v_params_2187_, 6);
lean_inc_ref(v_norm_2410_);
v_normProcs_2411_ = lean_ctor_get(v_params_2187_, 7);
lean_inc_ref(v_normProcs_2411_);
v_anchorRefs_x3f_2412_ = lean_ctor_get(v_params_2187_, 8);
lean_inc(v_anchorRefs_x3f_2412_);
lean_dec_ref(v_params_2187_);
v_size_2413_ = lean_ctor_get(v_extra_2331_, 2);
lean_inc(v_size_2413_);
v___y_2281_ = v_size_2413_;
v___y_2282_ = v_extensions_2406_;
v___y_2283_ = v___y_2310_;
v___y_2284_ = v___y_2311_;
v___y_2285_ = v_extra_2331_;
v___y_2286_ = v___y_2316_;
v___y_2287_ = v_extraFacts_2408_;
v___y_2288_ = v_config_2405_;
v___y_2289_ = v_normProcs_2411_;
v___y_2290_ = v_anchorRefs_x3f_2412_;
v___y_2291_ = v_norm_2410_;
v___y_2292_ = v_extraInj_2407_;
v___y_2293_ = v___y_2317_;
v___y_2294_ = v___y_2315_;
v___y_2295_ = v_symPrios_2409_;
v___y_2296_ = v___y_2314_;
goto v___jp_2280_;
}
default: 
{
lean_object* v_config_2414_; lean_object* v_extensions_2415_; lean_object* v_extraInj_2416_; lean_object* v_extraFacts_2417_; lean_object* v_symPrios_2418_; lean_object* v_norm_2419_; lean_object* v_normProcs_2420_; lean_object* v_anchorRefs_x3f_2421_; lean_object* v_size_2422_; 
v_config_2414_ = lean_ctor_get(v_params_2187_, 0);
lean_inc_ref(v_config_2414_);
v_extensions_2415_ = lean_ctor_get(v_params_2187_, 1);
lean_inc_ref(v_extensions_2415_);
v_extraInj_2416_ = lean_ctor_get(v_params_2187_, 3);
lean_inc_ref(v_extraInj_2416_);
v_extraFacts_2417_ = lean_ctor_get(v_params_2187_, 4);
lean_inc_ref(v_extraFacts_2417_);
v_symPrios_2418_ = lean_ctor_get(v_params_2187_, 5);
lean_inc_ref(v_symPrios_2418_);
v_norm_2419_ = lean_ctor_get(v_params_2187_, 6);
lean_inc_ref(v_norm_2419_);
v_normProcs_2420_ = lean_ctor_get(v_params_2187_, 7);
lean_inc_ref(v_normProcs_2420_);
v_anchorRefs_x3f_2421_ = lean_ctor_get(v_params_2187_, 8);
lean_inc(v_anchorRefs_x3f_2421_);
lean_dec_ref(v_params_2187_);
v_size_2422_ = lean_ctor_get(v_extra_2331_, 2);
lean_inc(v_size_2422_);
v___y_2245_ = v_extraFacts_2417_;
v___y_2246_ = v_config_2414_;
v___y_2247_ = v_normProcs_2420_;
v___y_2248_ = v_anchorRefs_x3f_2421_;
v___y_2249_ = v_norm_2419_;
v___y_2250_ = v_extraInj_2416_;
v___y_2251_ = v_size_2422_;
v___y_2252_ = v_extensions_2415_;
v___y_2253_ = v_symPrios_2418_;
v___y_2254_ = v_extra_2331_;
v___y_2255_ = v___y_2311_;
v___y_2256_ = v___y_2310_;
v___y_2257_ = v___y_2314_;
v___y_2258_ = v___y_2315_;
v___y_2259_ = v___y_2316_;
v___y_2260_ = v___y_2317_;
goto v___jp_2244_;
}
}
}
}
}
v___jp_2423_:
{
lean_object* v___x_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___f_2434_; lean_object* v___x_2435_; 
v___x_2431_ = lean_box(0);
v___x_2432_ = 1;
v___x_2433_ = lean_box(v___x_2432_);
lean_inc(v_p_2188_);
v___f_2434_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2434_, 0, v_p_2188_);
lean_closure_set(v___f_2434_, 1, v_term_2190_);
lean_closure_set(v___f_2434_, 2, v___x_2431_);
lean_closure_set(v___f_2434_, 3, v___x_2433_);
v___x_2435_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2434_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2480_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2480_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2480_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
if (lean_obj_tag(v_a_2436_) == 1)
{
lean_object* v_val_2440_; lean_object* v_fst_2441_; lean_object* v_snd_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___f_2445_; lean_object* v___x_2446_; 
lean_del_object(v___x_2438_);
v_val_2440_ = lean_ctor_get(v_a_2436_, 0);
lean_inc(v_val_2440_);
lean_dec_ref_known(v_a_2436_, 1);
v_fst_2441_ = lean_ctor_get(v_val_2440_, 0);
lean_inc_n(v_fst_2441_, 2);
v_snd_2442_ = lean_ctor_get(v_val_2440_, 1);
lean_inc_n(v_snd_2442_, 3);
lean_dec(v_val_2440_);
v___x_2443_ = lean_box(v___x_2432_);
v___x_2444_ = lean_box(v_minIndexable_2191_);
lean_inc_ref(v_params_2187_);
v___f_2445_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2445_, 0, v_params_2187_);
lean_closure_set(v___f_2445_, 1, v_p_2188_);
lean_closure_set(v___f_2445_, 2, v_fst_2441_);
lean_closure_set(v___f_2445_, 3, v_snd_2442_);
lean_closure_set(v___f_2445_, 4, v___x_2443_);
lean_closure_set(v___f_2445_, 5, v___x_2444_);
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2429_);
lean_inc(v___y_2428_);
lean_inc_ref(v___y_2427_);
v___x_2446_ = lean_infer_type(v_snd_2442_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2448_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc_n(v_a_2447_, 2);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2448_ = l_Lean_Meta_isProp(v_a_2447_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; uint8_t v___x_2450_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
v___x_2450_ = lean_unbox(v_a_2449_);
lean_dec(v_a_2449_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec(v_a_2447_);
lean_dec_ref(v___f_2445_);
lean_dec(v_snd_2442_);
lean_dec(v_fst_2441_);
lean_dec(v_kind_2424_);
lean_dec(v_mod_x3f_2189_);
lean_dec_ref(v_params_2187_);
v___x_2451_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2452_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2451_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec_ref(v___y_2429_);
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
else
{
v___y_2307_ = v_fst_2441_;
v___y_2308_ = v_a_2447_;
v___y_2309_ = v_snd_2442_;
v___y_2310_ = v___f_2445_;
v___y_2311_ = v_kind_2424_;
v___y_2312_ = v___y_2425_;
v___y_2313_ = v___y_2426_;
v___y_2314_ = v___y_2427_;
v___y_2315_ = v___y_2428_;
v___y_2316_ = v___y_2429_;
v___y_2317_ = v___y_2430_;
goto v___jp_2306_;
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_a_2447_);
lean_dec_ref(v___f_2445_);
lean_dec(v_snd_2442_);
lean_dec(v_fst_2441_);
lean_dec_ref(v___y_2429_);
lean_dec(v_kind_2424_);
lean_dec(v_mod_x3f_2189_);
lean_dec_ref(v_params_2187_);
v_a_2461_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2448_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2448_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v___f_2445_);
lean_dec(v_snd_2442_);
lean_dec(v_fst_2441_);
lean_dec_ref(v___y_2429_);
lean_dec(v_kind_2424_);
lean_dec(v_mod_x3f_2189_);
lean_dec_ref(v_params_2187_);
v_a_2469_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2446_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2446_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v___x_2478_; 
lean_dec(v_a_2436_);
lean_dec_ref(v___y_2429_);
lean_dec(v_kind_2424_);
lean_dec(v_mod_x3f_2189_);
lean_dec(v_p_2188_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v_params_2187_);
v___x_2478_ = v___x_2438_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_params_2187_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v___y_2429_);
lean_dec(v_kind_2424_);
lean_dec(v_mod_x3f_2189_);
lean_dec(v_p_2188_);
lean_dec_ref(v_params_2187_);
v_a_2481_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2435_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2435_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
v___jp_2489_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
v___x_2496_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2497_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2496_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec_ref(v___y_2494_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
v___jp_2506_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
v___x_2513_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2514_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2513_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec_ref(v___y_2511_);
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2514_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2514_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
v___jp_2523_:
{
lean_object* v___x_2530_; 
v___x_2530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_kind_2424_ = v___x_2530_;
v___y_2425_ = v___y_2524_;
v___y_2426_ = v___y_2525_;
v___y_2427_ = v___y_2526_;
v___y_2428_ = v___y_2527_;
v___y_2429_ = v___y_2528_;
v___y_2430_ = v___y_2529_;
goto v___jp_2423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2580_, lean_object* v_p_2581_, lean_object* v_mod_x3f_2582_, lean_object* v_term_2583_, lean_object* v_minIndexable_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
uint8_t v_minIndexable_boxed_2592_; lean_object* v_res_2593_; 
v_minIndexable_boxed_2592_ = lean_unbox(v_minIndexable_2584_);
v_res_2593_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2580_, v_p_2581_, v_mod_x3f_2582_, v_term_2583_, v_minIndexable_boxed_2592_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object* v_00_u03b1_2594_, lean_object* v_msg_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v_00_u03b1_2604_, lean_object* v_msg_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v_00_u03b1_2604_, v_msg_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object* v_msgData_2614_, lean_object* v_macroStack_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2614_, v_macroStack_2615_, v___y_2620_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object* v_msgData_2624_, lean_object* v_macroStack_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(v_msgData_2624_, v_macroStack_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2634_, lean_object* v_val_2635_, lean_object* v___x_2636_, lean_object* v_____r_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___x_2645_; lean_object* v_ext_2646_; lean_object* v_toEnvExtension_2647_; lean_object* v_env_2648_; lean_object* v_config_2649_; lean_object* v_extensions_2650_; lean_object* v_extra_2651_; lean_object* v_extraInj_2652_; lean_object* v_extraFacts_2653_; lean_object* v_symPrios_2654_; lean_object* v_norm_2655_; lean_object* v_normProcs_2656_; lean_object* v_anchorRefs_x3f_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2669_; 
v___x_2645_ = lean_st_ref_get(v___y_2643_);
v_ext_2646_ = lean_ctor_get(v_val_2635_, 1);
v_toEnvExtension_2647_ = lean_ctor_get(v_ext_2646_, 0);
v_env_2648_ = lean_ctor_get(v___x_2645_, 0);
lean_inc_ref(v_env_2648_);
lean_dec(v___x_2645_);
v_config_2649_ = lean_ctor_get(v_params_2634_, 0);
v_extensions_2650_ = lean_ctor_get(v_params_2634_, 1);
v_extra_2651_ = lean_ctor_get(v_params_2634_, 2);
v_extraInj_2652_ = lean_ctor_get(v_params_2634_, 3);
v_extraFacts_2653_ = lean_ctor_get(v_params_2634_, 4);
v_symPrios_2654_ = lean_ctor_get(v_params_2634_, 5);
v_norm_2655_ = lean_ctor_get(v_params_2634_, 6);
v_normProcs_2656_ = lean_ctor_get(v_params_2634_, 7);
v_anchorRefs_x3f_2657_ = lean_ctor_get(v_params_2634_, 8);
v_isSharedCheck_2669_ = !lean_is_exclusive(v_params_2634_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2659_ = v_params_2634_;
v_isShared_2660_ = v_isSharedCheck_2669_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_anchorRefs_x3f_2657_);
lean_inc(v_normProcs_2656_);
lean_inc(v_norm_2655_);
lean_inc(v_symPrios_2654_);
lean_inc(v_extraFacts_2653_);
lean_inc(v_extraInj_2652_);
lean_inc(v_extra_2651_);
lean_inc(v_extensions_2650_);
lean_inc(v_config_2649_);
lean_dec(v_params_2634_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2669_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v_asyncMode_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; 
v_asyncMode_2661_ = lean_ctor_get(v_toEnvExtension_2647_, 2);
v___x_2662_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2636_, v_val_2635_, v_env_2648_, v_asyncMode_2661_);
v___x_2663_ = lean_array_push(v_extensions_2650_, v___x_2662_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2663_);
v___x_2665_ = v___x_2659_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_config_2649_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2668_, 2, v_extra_2651_);
lean_ctor_set(v_reuseFailAlloc_2668_, 3, v_extraInj_2652_);
lean_ctor_set(v_reuseFailAlloc_2668_, 4, v_extraFacts_2653_);
lean_ctor_set(v_reuseFailAlloc_2668_, 5, v_symPrios_2654_);
lean_ctor_set(v_reuseFailAlloc_2668_, 6, v_norm_2655_);
lean_ctor_set(v_reuseFailAlloc_2668_, 7, v_normProcs_2656_);
lean_ctor_set(v_reuseFailAlloc_2668_, 8, v_anchorRefs_x3f_2657_);
v___x_2665_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
return v___x_2667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2670_, lean_object* v_val_2671_, lean_object* v___x_2672_, lean_object* v_____r_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2670_, v_val_2671_, v___x_2672_, v_____r_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v___x_2672_);
lean_dec_ref(v_val_2671_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2682_, lean_object* v_id_2683_, uint8_t v_minIndexable_2684_, lean_object* v_as_x27_2685_, lean_object* v_b_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
if (lean_obj_tag(v_as_x27_2685_) == 0)
{
lean_object* v___x_2692_; 
lean_dec(v_id_2683_);
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_b_2686_);
return v___x_2692_;
}
else
{
lean_object* v_head_2693_; lean_object* v_tail_2694_; lean_object* v_toCold_2695_; lean_object* v_currRecDepth_2696_; lean_object* v_ref_2697_; uint16_t v_optionFlags_2698_; uint8_t v_suppressElabErrors_2699_; uint8_t v_isRecordingDeps_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v_ref_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_head_2693_ = lean_ctor_get(v_as_x27_2685_, 0);
v_tail_2694_ = lean_ctor_get(v_as_x27_2685_, 1);
v_toCold_2695_ = lean_ctor_get(v___y_2689_, 0);
v_currRecDepth_2696_ = lean_ctor_get(v___y_2689_, 1);
v_ref_2697_ = lean_ctor_get(v___y_2689_, 2);
v_optionFlags_2698_ = lean_ctor_get_uint16(v___y_2689_, sizeof(void*)*3);
v_suppressElabErrors_2699_ = lean_ctor_get_uint8(v___y_2689_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2700_ = lean_ctor_get_uint8(v___y_2689_, sizeof(void*)*3 + 3);
v___x_2701_ = 0;
v___x_2702_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_2703_ = l_Lean_replaceRef(v_p_2682_, v_ref_2697_);
lean_inc(v_currRecDepth_2696_);
lean_inc_ref(v_toCold_2695_);
v___x_2704_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2704_, 0, v_toCold_2695_);
lean_ctor_set(v___x_2704_, 1, v_currRecDepth_2696_);
lean_ctor_set(v___x_2704_, 2, v_ref_2703_);
lean_ctor_set_uint16(v___x_2704_, sizeof(void*)*3, v_optionFlags_2698_);
lean_ctor_set_uint8(v___x_2704_, sizeof(void*)*3 + 2, v_suppressElabErrors_2699_);
lean_ctor_set_uint8(v___x_2704_, sizeof(void*)*3 + 3, v_isRecordingDeps_2700_);
lean_inc(v_head_2693_);
lean_inc(v_id_2683_);
v___x_2705_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2686_, v_id_2683_, v_head_2693_, v___x_2702_, v_minIndexable_2684_, v___x_2701_, v___x_2701_, v___y_2687_, v___y_2688_, v___x_2704_, v___y_2690_);
lean_dec_ref_known(v___x_2704_, 3);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v_as_x27_2685_ = v_tail_2694_;
v_b_2686_ = v_a_2706_;
goto _start;
}
else
{
lean_dec(v_id_2683_);
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_2708_, lean_object* v_id_2709_, lean_object* v_minIndexable_2710_, lean_object* v_as_x27_2711_, lean_object* v_b_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
uint8_t v_minIndexable_boxed_2718_; lean_object* v_res_2719_; 
v_minIndexable_boxed_2718_ = lean_unbox(v_minIndexable_2710_);
v_res_2719_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2708_, v_id_2709_, v_minIndexable_boxed_2718_, v_as_x27_2711_, v_b_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v_as_x27_2711_);
lean_dec(v_p_2708_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
if (lean_obj_tag(v_a_2721_) == 0)
{
lean_object* v___x_2723_; 
v___x_2723_ = l_List_reverse___redArg(v_a_2722_);
return v___x_2723_;
}
else
{
lean_object* v_head_2724_; lean_object* v_tail_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2736_; 
v_head_2724_ = lean_ctor_get(v_a_2721_, 0);
v_tail_2725_ = lean_ctor_get(v_a_2721_, 1);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_a_2721_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2727_ = v_a_2721_;
v_isShared_2728_ = v_isSharedCheck_2736_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_tail_2725_);
lean_inc(v_head_2724_);
lean_dec(v_a_2721_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2736_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v_kind_2729_; uint8_t v___x_2730_; 
v_kind_2729_ = lean_ctor_get(v_head_2724_, 6);
v___x_2730_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_2729_, v_k_2720_);
if (v___x_2730_ == 0)
{
lean_del_object(v___x_2727_);
lean_dec(v_head_2724_);
v_a_2721_ = v_tail_2725_;
goto _start;
}
else
{
lean_object* v___x_2733_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 1, v_a_2722_);
v___x_2733_ = v___x_2727_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_head_2724_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_a_2722_);
v___x_2733_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
v_a_2721_ = v_tail_2725_;
v_a_2722_ = v___x_2733_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_2737_, v_a_2738_, v_a_2739_);
lean_dec(v_k_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_2741_, lean_object* v_msg_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_toCold_2750_; lean_object* v_currRecDepth_2751_; lean_object* v_ref_2752_; uint16_t v_optionFlags_2753_; uint8_t v_suppressElabErrors_2754_; uint8_t v_isRecordingDeps_2755_; lean_object* v_ref_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_toCold_2750_ = lean_ctor_get(v___y_2747_, 0);
v_currRecDepth_2751_ = lean_ctor_get(v___y_2747_, 1);
v_ref_2752_ = lean_ctor_get(v___y_2747_, 2);
v_optionFlags_2753_ = lean_ctor_get_uint16(v___y_2747_, sizeof(void*)*3);
v_suppressElabErrors_2754_ = lean_ctor_get_uint8(v___y_2747_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2755_ = lean_ctor_get_uint8(v___y_2747_, sizeof(void*)*3 + 3);
v_ref_2756_ = l_Lean_replaceRef(v_ref_2741_, v_ref_2752_);
lean_inc(v_currRecDepth_2751_);
lean_inc_ref(v_toCold_2750_);
v___x_2757_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2757_, 0, v_toCold_2750_);
lean_ctor_set(v___x_2757_, 1, v_currRecDepth_2751_);
lean_ctor_set(v___x_2757_, 2, v_ref_2756_);
lean_ctor_set_uint16(v___x_2757_, sizeof(void*)*3, v_optionFlags_2753_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*3 + 2, v_suppressElabErrors_2754_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*3 + 3, v_isRecordingDeps_2755_);
v___x_2758_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___x_2757_, v___y_2748_);
lean_dec_ref_known(v___x_2757_, 3);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_2759_, lean_object* v_msg_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_2759_, v_msg_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v_ref_2759_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_2769_, lean_object* v_id_2770_, uint8_t v_minIndexable_2771_, lean_object* v_as_x27_2772_, lean_object* v_b_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
if (lean_obj_tag(v_as_x27_2772_) == 0)
{
lean_object* v___x_2779_; 
lean_dec(v_id_2770_);
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v_b_2773_);
return v___x_2779_;
}
else
{
lean_object* v_head_2780_; lean_object* v_tail_2781_; lean_object* v_toCold_2782_; lean_object* v_currRecDepth_2783_; lean_object* v_ref_2784_; uint16_t v_optionFlags_2785_; uint8_t v_suppressElabErrors_2786_; uint8_t v_isRecordingDeps_2787_; uint8_t v___x_2788_; uint8_t v___x_2789_; lean_object* v___x_2790_; lean_object* v_ref_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_head_2780_ = lean_ctor_get(v_as_x27_2772_, 0);
v_tail_2781_ = lean_ctor_get(v_as_x27_2772_, 1);
v_toCold_2782_ = lean_ctor_get(v___y_2776_, 0);
v_currRecDepth_2783_ = lean_ctor_get(v___y_2776_, 1);
v_ref_2784_ = lean_ctor_get(v___y_2776_, 2);
v_optionFlags_2785_ = lean_ctor_get_uint16(v___y_2776_, sizeof(void*)*3);
v_suppressElabErrors_2786_ = lean_ctor_get_uint8(v___y_2776_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2787_ = lean_ctor_get_uint8(v___y_2776_, sizeof(void*)*3 + 3);
v___x_2788_ = 0;
v___x_2789_ = 1;
v___x_2790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_2791_ = l_Lean_replaceRef(v_p_2769_, v_ref_2784_);
lean_inc(v_currRecDepth_2783_);
lean_inc_ref(v_toCold_2782_);
v___x_2792_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2792_, 0, v_toCold_2782_);
lean_ctor_set(v___x_2792_, 1, v_currRecDepth_2783_);
lean_ctor_set(v___x_2792_, 2, v_ref_2791_);
lean_ctor_set_uint16(v___x_2792_, sizeof(void*)*3, v_optionFlags_2785_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*3 + 2, v_suppressElabErrors_2786_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*3 + 3, v_isRecordingDeps_2787_);
lean_inc(v_head_2780_);
lean_inc(v_id_2770_);
v___x_2793_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2773_, v_id_2770_, v_head_2780_, v___x_2790_, v_minIndexable_2771_, v___x_2788_, v___x_2789_, v___y_2774_, v___y_2775_, v___x_2792_, v___y_2777_);
lean_dec_ref_known(v___x_2792_, 3);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2793_, 1);
v_as_x27_2772_ = v_tail_2781_;
v_b_2773_ = v_a_2794_;
goto _start;
}
else
{
lean_dec(v_id_2770_);
return v___x_2793_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_2796_, lean_object* v_id_2797_, lean_object* v_minIndexable_2798_, lean_object* v_as_x27_2799_, lean_object* v_b_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
uint8_t v_minIndexable_boxed_2806_; lean_object* v_res_2807_; 
v_minIndexable_boxed_2806_ = lean_unbox(v_minIndexable_2798_);
v_res_2807_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_2796_, v_id_2797_, v_minIndexable_boxed_2806_, v_as_x27_2799_, v_b_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v_as_x27_2799_);
lean_dec(v_p_2796_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_2808_){
_start:
{
if (lean_obj_tag(v_x_2808_) == 0)
{
lean_object* v___x_2809_; 
v___x_2809_ = lean_box(0);
return v___x_2809_;
}
else
{
lean_object* v_head_2810_; lean_object* v_tail_2811_; lean_object* v_fst_2812_; uint8_t v___x_2813_; 
v_head_2810_ = lean_ctor_get(v_x_2808_, 0);
v_tail_2811_ = lean_ctor_get(v_x_2808_, 1);
v_fst_2812_ = lean_ctor_get(v_head_2810_, 0);
v___x_2813_ = l_Lean_isPrivateName(v_fst_2812_);
if (v___x_2813_ == 0)
{
v_x_2808_ = v_tail_2811_;
goto _start;
}
else
{
lean_object* v___x_2815_; 
lean_inc(v_head_2810_);
v___x_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2815_, 0, v_head_2810_);
return v___x_2815_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_2816_);
lean_dec(v_x_2816_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_2818_, lean_object* v_msgData_2819_, uint8_t v_severity_2820_, uint8_t v_isSilent_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v___y_2828_; uint8_t v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; uint8_t v___y_2833_; lean_object* v___y_2834_; lean_object* v_toCold_2835_; lean_object* v___y_2836_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; uint8_t v___y_2868_; uint8_t v___y_2869_; uint8_t v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2892_; lean_object* v___y_2893_; uint8_t v___y_2894_; lean_object* v___y_2895_; uint8_t v___y_2896_; uint8_t v___y_2897_; lean_object* v___y_2898_; uint8_t v___y_2902_; uint8_t v___y_2903_; uint8_t v___y_2904_; uint8_t v___x_2915_; uint8_t v___y_2917_; uint8_t v___y_2918_; uint8_t v___y_2919_; uint8_t v___y_2921_; uint8_t v___x_2929_; 
v___x_2915_ = 2;
v___x_2929_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2820_, v___x_2915_);
if (v___x_2929_ == 0)
{
v___y_2921_ = v___x_2929_;
goto v___jp_2920_;
}
else
{
uint8_t v___x_2930_; 
lean_inc_ref(v_msgData_2819_);
v___x_2930_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2819_);
v___y_2921_ = v___x_2930_;
goto v___jp_2920_;
}
v___jp_2827_:
{
lean_object* v_currNamespace_2837_; lean_object* v_openDecls_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v_env_2843_; lean_object* v_nextMacroScope_2844_; lean_object* v_ngen_2845_; lean_object* v_auxDeclNGen_2846_; lean_object* v_traceState_2847_; lean_object* v_cache_2848_; lean_object* v_recordedDeps_2849_; lean_object* v_messages_2850_; lean_object* v_infoState_2851_; lean_object* v_snapshotTasks_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2863_; 
v_currNamespace_2837_ = lean_ctor_get(v_toCold_2835_, 4);
v_openDecls_2838_ = lean_ctor_get(v_toCold_2835_, 5);
lean_inc(v_openDecls_2838_);
lean_inc(v_currNamespace_2837_);
v___x_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2839_, 0, v_currNamespace_2837_);
lean_ctor_set(v___x_2839_, 1, v_openDecls_2838_);
v___x_2840_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v___y_2828_);
lean_inc_ref(v___y_2834_);
lean_inc_ref(v___y_2831_);
v___x_2841_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2841_, 0, v___y_2831_);
lean_ctor_set(v___x_2841_, 1, v___y_2832_);
lean_ctor_set(v___x_2841_, 2, v___y_2830_);
lean_ctor_set(v___x_2841_, 3, v___y_2834_);
lean_ctor_set(v___x_2841_, 4, v___x_2840_);
lean_ctor_set_uint8(v___x_2841_, sizeof(void*)*5, v___y_2833_);
lean_ctor_set_uint8(v___x_2841_, sizeof(void*)*5 + 1, v___y_2829_);
lean_ctor_set_uint8(v___x_2841_, sizeof(void*)*5 + 2, v_isSilent_2821_);
v___x_2842_ = lean_st_ref_take(v___y_2836_);
v_env_2843_ = lean_ctor_get(v___x_2842_, 0);
v_nextMacroScope_2844_ = lean_ctor_get(v___x_2842_, 1);
v_ngen_2845_ = lean_ctor_get(v___x_2842_, 2);
v_auxDeclNGen_2846_ = lean_ctor_get(v___x_2842_, 3);
v_traceState_2847_ = lean_ctor_get(v___x_2842_, 4);
v_cache_2848_ = lean_ctor_get(v___x_2842_, 5);
v_recordedDeps_2849_ = lean_ctor_get(v___x_2842_, 6);
v_messages_2850_ = lean_ctor_get(v___x_2842_, 7);
v_infoState_2851_ = lean_ctor_get(v___x_2842_, 8);
v_snapshotTasks_2852_ = lean_ctor_get(v___x_2842_, 9);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2854_ = v___x_2842_;
v_isShared_2855_ = v_isSharedCheck_2863_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_snapshotTasks_2852_);
lean_inc(v_infoState_2851_);
lean_inc(v_messages_2850_);
lean_inc(v_recordedDeps_2849_);
lean_inc(v_cache_2848_);
lean_inc(v_traceState_2847_);
lean_inc(v_auxDeclNGen_2846_);
lean_inc(v_ngen_2845_);
lean_inc(v_nextMacroScope_2844_);
lean_inc(v_env_2843_);
lean_dec(v___x_2842_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2863_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2856_ = lean_box(0);
v___x_2857_ = l_Lean_MessageLog_add(v___x_2841_, v_messages_2850_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 7, v___x_2857_);
v___x_2859_ = v___x_2854_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_env_2843_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_nextMacroScope_2844_);
lean_ctor_set(v_reuseFailAlloc_2862_, 2, v_ngen_2845_);
lean_ctor_set(v_reuseFailAlloc_2862_, 3, v_auxDeclNGen_2846_);
lean_ctor_set(v_reuseFailAlloc_2862_, 4, v_traceState_2847_);
lean_ctor_set(v_reuseFailAlloc_2862_, 5, v_cache_2848_);
lean_ctor_set(v_reuseFailAlloc_2862_, 6, v_recordedDeps_2849_);
lean_ctor_set(v_reuseFailAlloc_2862_, 7, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2862_, 8, v_infoState_2851_);
lean_ctor_set(v_reuseFailAlloc_2862_, 9, v_snapshotTasks_2852_);
v___x_2859_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_st_ref_put(v___y_2836_, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2856_);
return v___x_2861_;
}
}
}
v___jp_2864_:
{
lean_object* v_fileName_2873_; lean_object* v_fileMap_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2890_; 
v_fileName_2873_ = lean_ctor_get(v___y_2867_, 0);
v_fileMap_2874_ = lean_ctor_get(v___y_2867_, 1);
v___x_2875_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2819_);
v___x_2876_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_2875_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2890_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2890_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_inc_ref_n(v_fileMap_2874_, 2);
v___x_2881_ = l_Lean_FileMap_toPosition(v_fileMap_2874_, v___y_2871_);
lean_dec(v___y_2871_);
v___x_2882_ = l_Lean_FileMap_toPosition(v_fileMap_2874_, v___y_2872_);
lean_dec(v___y_2872_);
v___x_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
v___x_2884_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_2870_ == 0)
{
lean_del_object(v___x_2879_);
lean_dec_ref(v___y_2866_);
v___y_2828_ = v_a_2877_;
v___y_2829_ = v___y_2868_;
v___y_2830_ = v___x_2883_;
v___y_2831_ = v_fileName_2873_;
v___y_2832_ = v___x_2881_;
v___y_2833_ = v___y_2869_;
v___y_2834_ = v___x_2884_;
v_toCold_2835_ = v___y_2865_;
v___y_2836_ = v___y_2825_;
goto v___jp_2827_;
}
else
{
uint8_t v___x_2885_; 
lean_inc(v_a_2877_);
v___x_2885_ = l_Lean_MessageData_hasTag(v___y_2866_, v_a_2877_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
lean_dec_ref_known(v___x_2883_, 1);
lean_dec_ref(v___x_2881_);
lean_dec(v_a_2877_);
v___x_2886_ = lean_box(0);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v___x_2886_);
v___x_2888_ = v___x_2879_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
else
{
lean_del_object(v___x_2879_);
v___y_2828_ = v_a_2877_;
v___y_2829_ = v___y_2868_;
v___y_2830_ = v___x_2883_;
v___y_2831_ = v_fileName_2873_;
v___y_2832_ = v___x_2881_;
v___y_2833_ = v___y_2869_;
v___y_2834_ = v___x_2884_;
v_toCold_2835_ = v___y_2865_;
v___y_2836_ = v___y_2825_;
goto v___jp_2827_;
}
}
}
}
v___jp_2891_:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_Syntax_getTailPos_x3f(v___y_2895_, v___y_2897_);
lean_dec(v___y_2895_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_inc(v___y_2898_);
v___y_2865_ = v___y_2892_;
v___y_2866_ = v___y_2893_;
v___y_2867_ = v___y_2892_;
v___y_2868_ = v___y_2896_;
v___y_2869_ = v___y_2897_;
v___y_2870_ = v___y_2894_;
v___y_2871_ = v___y_2898_;
v___y_2872_ = v___y_2898_;
goto v___jp_2864_;
}
else
{
lean_object* v_val_2900_; 
v_val_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_val_2900_);
lean_dec_ref_known(v___x_2899_, 1);
v___y_2865_ = v___y_2892_;
v___y_2866_ = v___y_2893_;
v___y_2867_ = v___y_2892_;
v___y_2868_ = v___y_2896_;
v___y_2869_ = v___y_2897_;
v___y_2870_ = v___y_2894_;
v___y_2871_ = v___y_2898_;
v___y_2872_ = v_val_2900_;
goto v___jp_2864_;
}
}
v___jp_2901_:
{
lean_object* v_toCold_2905_; lean_object* v_ref_2906_; uint8_t v_suppressElabErrors_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___f_2910_; lean_object* v_ref_2911_; lean_object* v___x_2912_; 
v_toCold_2905_ = lean_ctor_get(v___y_2824_, 0);
v_ref_2906_ = lean_ctor_get(v___y_2824_, 2);
v_suppressElabErrors_2907_ = lean_ctor_get_uint8(v___y_2824_, sizeof(void*)*3 + 2);
v___x_2908_ = lean_box(v_suppressElabErrors_2907_);
v___x_2909_ = lean_box(v___y_2902_);
v___f_2910_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2910_, 0, v___x_2908_);
lean_closure_set(v___f_2910_, 1, v___x_2909_);
v_ref_2911_ = l_Lean_replaceRef(v_ref_2818_, v_ref_2906_);
v___x_2912_ = l_Lean_Syntax_getPos_x3f(v_ref_2911_, v___y_2903_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_unsigned_to_nat(0u);
v___y_2892_ = v_toCold_2905_;
v___y_2893_ = v___f_2910_;
v___y_2894_ = v_suppressElabErrors_2907_;
v___y_2895_ = v_ref_2911_;
v___y_2896_ = v___y_2904_;
v___y_2897_ = v___y_2903_;
v___y_2898_ = v___x_2913_;
goto v___jp_2891_;
}
else
{
lean_object* v_val_2914_; 
v_val_2914_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_val_2914_);
lean_dec_ref_known(v___x_2912_, 1);
v___y_2892_ = v_toCold_2905_;
v___y_2893_ = v___f_2910_;
v___y_2894_ = v_suppressElabErrors_2907_;
v___y_2895_ = v_ref_2911_;
v___y_2896_ = v___y_2904_;
v___y_2897_ = v___y_2903_;
v___y_2898_ = v_val_2914_;
goto v___jp_2891_;
}
}
v___jp_2916_:
{
if (v___y_2919_ == 0)
{
v___y_2902_ = v___y_2917_;
v___y_2903_ = v___y_2918_;
v___y_2904_ = v_severity_2820_;
goto v___jp_2901_;
}
else
{
v___y_2902_ = v___y_2917_;
v___y_2903_ = v___y_2918_;
v___y_2904_ = v___x_2915_;
goto v___jp_2901_;
}
}
v___jp_2920_:
{
if (v___y_2921_ == 0)
{
uint8_t v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = 1;
v___x_2923_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2820_, v___x_2922_);
if (v___x_2923_ == 0)
{
v___y_2917_ = v___y_2921_;
v___y_2918_ = v___y_2921_;
v___y_2919_ = v___x_2923_;
goto v___jp_2916_;
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2924_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2824_);
v___x_2925_ = l_Lean_warningAsError;
v___x_2926_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_2924_, v___x_2925_);
lean_dec_ref(v___x_2924_);
v___y_2917_ = v___y_2921_;
v___y_2918_ = v___y_2921_;
v___y_2919_ = v___x_2926_;
goto v___jp_2916_;
}
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
lean_dec_ref(v_msgData_2819_);
v___x_2927_ = lean_box(0);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_2931_, lean_object* v_msgData_2932_, lean_object* v_severity_2933_, lean_object* v_isSilent_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
uint8_t v_severity_boxed_2940_; uint8_t v_isSilent_boxed_2941_; lean_object* v_res_2942_; 
v_severity_boxed_2940_ = lean_unbox(v_severity_2933_);
v_isSilent_boxed_2941_ = lean_unbox(v_isSilent_2934_);
v_res_2942_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_2931_, v_msgData_2932_, v_severity_boxed_2940_, v_isSilent_boxed_2941_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v_ref_2931_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_2943_, uint8_t v_severity_2944_, uint8_t v_isSilent_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v_ref_2953_; lean_object* v___x_2954_; 
v_ref_2953_ = lean_ctor_get(v___y_2950_, 2);
v___x_2954_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_2953_, v_msgData_2943_, v_severity_2944_, v_isSilent_2945_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_2955_, lean_object* v_severity_2956_, lean_object* v_isSilent_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
uint8_t v_severity_boxed_2965_; uint8_t v_isSilent_boxed_2966_; lean_object* v_res_2967_; 
v_severity_boxed_2965_ = lean_unbox(v_severity_2956_);
v_isSilent_boxed_2966_ = lean_unbox(v_isSilent_2957_);
v_res_2967_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_2955_, v_severity_boxed_2965_, v_isSilent_boxed_2966_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
uint8_t v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = 1;
v___x_2977_ = 0;
v___x_2978_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_2968_, v___x_2976_, v___x_2977_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v___x_2991_; uint8_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2991_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2989_);
v___x_2992_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_2991_, v_opt_2988_);
lean_dec_ref(v___x_2991_);
v___x_2993_ = lean_box(v___x_2992_);
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_2995_, v___y_2996_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v_opt_2995_);
return v_res_2998_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3001_ = l_Lean_stringToMessageData(v___x_3000_);
return v___x_3001_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3004_ = l_Lean_stringToMessageData(v___x_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; lean_object* v_env_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3036_; 
v___x_3013_ = lean_st_ref_get(v___y_3011_);
v_env_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc_ref(v_env_3014_);
lean_dec(v___x_3013_);
v___x_3015_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3016_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3015_, v___y_3010_);
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3019_ = v___x_3016_;
v_isShared_3020_ = v_isSharedCheck_3036_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3036_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
uint8_t v_isExporting_3026_; 
v_isExporting_3026_ = lean_ctor_get_uint8(v_env_3014_, sizeof(void*)*8);
lean_dec_ref(v_env_3014_);
if (v_isExporting_3026_ == 0)
{
lean_dec(v_a_3017_);
lean_dec(v_id_3005_);
goto v___jp_3021_;
}
else
{
uint8_t v___x_3027_; 
v___x_3027_ = l_Lean_isPrivateName(v_id_3005_);
if (v___x_3027_ == 0)
{
lean_dec(v_a_3017_);
lean_dec(v_id_3005_);
goto v___jp_3021_;
}
else
{
uint8_t v___x_3028_; 
v___x_3028_ = lean_unbox(v_a_3017_);
lean_dec(v_a_3017_);
if (v___x_3028_ == 0)
{
lean_dec(v_id_3005_);
goto v___jp_3021_;
}
else
{
lean_object* v___x_3029_; uint8_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_del_object(v___x_3019_);
v___x_3029_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3030_ = 0;
v___x_3031_ = l_Lean_MessageData_ofConstName(v_id_3005_, v___x_3030_);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3029_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3034_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
return v___x_3035_;
}
}
}
v___jp_3021_:
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3022_ = lean_box(0);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v___x_3022_);
v___x_3024_ = v___x_3019_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3046_, uint8_t v_enableLog_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v___x_3055_; lean_object* v_toCold_3056_; lean_object* v_env_3057_; lean_object* v_currNamespace_3058_; lean_object* v_openDecls_3059_; lean_object* v___x_3060_; lean_object* v_res_3061_; lean_object* v___x_3062_; 
v___x_3055_ = lean_st_ref_get(v___y_3053_);
v_toCold_3056_ = lean_ctor_get(v___y_3052_, 0);
v_env_3057_ = lean_ctor_get(v___x_3055_, 0);
lean_inc_ref(v_env_3057_);
lean_dec(v___x_3055_);
v_currNamespace_3058_ = lean_ctor_get(v_toCold_3056_, 4);
v_openDecls_3059_ = lean_ctor_get(v_toCold_3056_, 5);
v___x_3060_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3052_);
lean_inc(v_openDecls_3059_);
lean_inc(v_currNamespace_3058_);
v_res_3061_ = l_Lean_ResolveName_resolveGlobalName(v_env_3057_, v___x_3060_, v_currNamespace_3058_, v_openDecls_3059_, v_id_3046_);
lean_dec_ref(v___x_3060_);
v___x_3062_ = lean_st_ref_get(v___y_3053_);
if (v_enableLog_3047_ == 0)
{
lean_object* v___x_3063_; 
lean_dec(v___x_3062_);
v___x_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3063_, 0, v_res_3061_);
return v___x_3063_;
}
else
{
lean_object* v_env_3064_; uint8_t v_isExporting_3065_; 
v_env_3064_ = lean_ctor_get(v___x_3062_, 0);
lean_inc_ref(v_env_3064_);
lean_dec(v___x_3062_);
v_isExporting_3065_ = lean_ctor_get_uint8(v_env_3064_, sizeof(void*)*8);
lean_dec_ref(v_env_3064_);
if (v_isExporting_3065_ == 0)
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v_res_3061_);
return v___x_3066_;
}
else
{
lean_object* v___x_3067_; 
v___x_3067_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3061_);
if (lean_obj_tag(v___x_3067_) == 1)
{
lean_object* v_val_3068_; lean_object* v_fst_3069_; lean_object* v___x_3070_; 
v_val_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_val_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v_fst_3069_ = lean_ctor_get(v_val_3068_, 0);
lean_inc(v_fst_3069_);
lean_dec(v_val_3068_);
v___x_3070_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3069_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v___x_3070_, 0);
lean_dec(v_unused_3078_);
v___x_3072_ = v___x_3070_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_dec(v___x_3070_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v_res_3061_);
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_res_3061_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v_res_3061_);
v_a_3079_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3070_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3070_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v___x_3087_; 
lean_dec(v___x_3067_);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v_res_3061_);
return v___x_3087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3088_, lean_object* v_enableLog_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
uint8_t v_enableLog_boxed_3097_; lean_object* v_res_3098_; 
v_enableLog_boxed_3097_ = lean_unbox(v_enableLog_3089_);
v_res_3098_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3088_, v_enableLog_boxed_3097_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
if (lean_obj_tag(v_a_3099_) == 0)
{
lean_object* v___x_3101_; 
v___x_3101_ = l_List_reverse___redArg(v_a_3100_);
return v___x_3101_;
}
else
{
lean_object* v_head_3102_; lean_object* v_tail_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3114_; 
v_head_3102_ = lean_ctor_get(v_a_3099_, 0);
v_tail_3103_ = lean_ctor_get(v_a_3099_, 1);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_a_3099_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3105_ = v_a_3099_;
v_isShared_3106_ = v_isSharedCheck_3114_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_tail_3103_);
lean_inc(v_head_3102_);
lean_dec(v_a_3099_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3114_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v_snd_3107_; uint8_t v___x_3108_; 
v_snd_3107_ = lean_ctor_get(v_head_3102_, 1);
v___x_3108_ = l_List_isEmpty___redArg(v_snd_3107_);
if (v___x_3108_ == 0)
{
lean_del_object(v___x_3105_);
lean_dec(v_head_3102_);
v_a_3099_ = v_tail_3103_;
goto _start;
}
else
{
lean_object* v___x_3111_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 1, v_a_3100_);
v___x_3111_ = v___x_3105_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_head_3102_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_a_3100_);
v___x_3111_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
v_a_3099_ = v_tail_3103_;
v_a_3100_ = v___x_3111_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3115_, lean_object* v_findLocalDecl_x3f_3116_, lean_object* v_n_3117_, lean_object* v_projs_3118_, uint8_t v_globalDeclFound_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___y_3128_; lean_object* v___y_3129_; uint8_t v_globalDeclFoundNext_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v_imported_3139_; lean_object* v_ctx_3140_; lean_object* v_scopes_3141_; lean_object* v_givenNameView_3142_; uint8_t v___y_3144_; 
v_imported_3139_ = lean_ctor_get(v_view_3115_, 1);
v_ctx_3140_ = lean_ctor_get(v_view_3115_, 2);
v_scopes_3141_ = lean_ctor_get(v_view_3115_, 3);
lean_inc(v_scopes_3141_);
lean_inc(v_ctx_3140_);
lean_inc(v_imported_3139_);
lean_inc(v_n_3117_);
v_givenNameView_3142_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3142_, 0, v_n_3117_);
lean_ctor_set(v_givenNameView_3142_, 1, v_imported_3139_);
lean_ctor_set(v_givenNameView_3142_, 2, v_ctx_3140_);
lean_ctor_set(v_givenNameView_3142_, 3, v_scopes_3141_);
if (v_globalDeclFound_3119_ == 0)
{
v___y_3144_ = v_globalDeclFound_3119_;
goto v___jp_3143_;
}
else
{
uint8_t v___x_3179_; 
v___x_3179_ = l_List_isEmpty___redArg(v_projs_3118_);
if (v___x_3179_ == 0)
{
v___y_3144_ = v_globalDeclFound_3119_;
goto v___jp_3143_;
}
else
{
uint8_t v___x_3180_; 
v___x_3180_ = 0;
v___y_3144_ = v___x_3180_;
goto v___jp_3143_;
}
}
v___jp_3127_:
{
lean_object* v___x_3137_; 
v___x_3137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___y_3129_);
lean_ctor_set(v___x_3137_, 1, v_projs_3118_);
v_n_3117_ = v___y_3128_;
v_projs_3118_ = v___x_3137_;
v_globalDeclFound_3119_ = v_globalDeclFoundNext_3130_;
v___y_3120_ = v___y_3131_;
v___y_3121_ = v___y_3132_;
v___y_3122_ = v___y_3133_;
v___y_3123_ = v___y_3134_;
v___y_3124_ = v___y_3135_;
v___y_3125_ = v___y_3136_;
goto _start;
}
v___jp_3143_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_box(v___y_3144_);
lean_inc_ref(v_findLocalDecl_x3f_3116_);
lean_inc_ref(v_givenNameView_3142_);
v___x_3146_ = lean_apply_2(v_findLocalDecl_x3f_3116_, v_givenNameView_3142_, v___x_3145_);
if (lean_obj_tag(v___x_3146_) == 0)
{
if (lean_obj_tag(v_n_3117_) == 1)
{
if (v_globalDeclFound_3119_ == 0)
{
lean_object* v_pre_3147_; lean_object* v_str_3148_; uint8_t v_globalDeclFoundNext_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_pre_3147_ = lean_ctor_get(v_n_3117_, 0);
lean_inc(v_pre_3147_);
v_str_3148_ = lean_ctor_get(v_n_3117_, 1);
lean_inc_ref(v_str_3148_);
lean_dec_ref_known(v_n_3117_, 2);
v_globalDeclFoundNext_3149_ = 1;
v___x_3150_ = l_Lean_MacroScopesView_review(v_givenNameView_3142_);
v___x_3151_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3150_, v_globalDeclFound_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3153_; lean_object* v_r_3154_; uint8_t v___x_3155_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
v___x_3153_ = lean_box(0);
v_r_3154_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3152_, v___x_3153_);
v___x_3155_ = l_List_isEmpty___redArg(v_r_3154_);
lean_dec(v_r_3154_);
if (v___x_3155_ == 0)
{
v___y_3128_ = v_pre_3147_;
v___y_3129_ = v_str_3148_;
v_globalDeclFoundNext_3130_ = v_globalDeclFoundNext_3149_;
v___y_3131_ = v___y_3120_;
v___y_3132_ = v___y_3121_;
v___y_3133_ = v___y_3122_;
v___y_3134_ = v___y_3123_;
v___y_3135_ = v___y_3124_;
v___y_3136_ = v___y_3125_;
goto v___jp_3127_;
}
else
{
v___y_3128_ = v_pre_3147_;
v___y_3129_ = v_str_3148_;
v_globalDeclFoundNext_3130_ = v_globalDeclFound_3119_;
v___y_3131_ = v___y_3120_;
v___y_3132_ = v___y_3121_;
v___y_3133_ = v___y_3122_;
v___y_3134_ = v___y_3123_;
v___y_3135_ = v___y_3124_;
v___y_3136_ = v___y_3125_;
goto v___jp_3127_;
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v_str_3148_);
lean_dec(v_pre_3147_);
lean_dec(v_projs_3118_);
lean_dec_ref(v_findLocalDecl_x3f_3116_);
v_a_3156_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3151_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3151_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_pre_3164_; lean_object* v_str_3165_; 
lean_dec_ref_known(v_givenNameView_3142_, 4);
v_pre_3164_ = lean_ctor_get(v_n_3117_, 0);
lean_inc(v_pre_3164_);
v_str_3165_ = lean_ctor_get(v_n_3117_, 1);
lean_inc_ref(v_str_3165_);
lean_dec_ref_known(v_n_3117_, 2);
v___y_3128_ = v_pre_3164_;
v___y_3129_ = v_str_3165_;
v_globalDeclFoundNext_3130_ = v_globalDeclFound_3119_;
v___y_3131_ = v___y_3120_;
v___y_3132_ = v___y_3121_;
v___y_3133_ = v___y_3122_;
v___y_3134_ = v___y_3123_;
v___y_3135_ = v___y_3124_;
v___y_3136_ = v___y_3125_;
goto v___jp_3127_;
}
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_dec_ref_known(v_givenNameView_3142_, 4);
lean_dec(v_projs_3118_);
lean_dec(v_n_3117_);
lean_dec_ref(v_findLocalDecl_x3f_3116_);
v___x_3166_ = lean_box(0);
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
}
else
{
lean_object* v_val_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3178_; 
lean_dec_ref_known(v_givenNameView_3142_, 4);
lean_dec(v_n_3117_);
lean_dec_ref(v_findLocalDecl_x3f_3116_);
v_val_3168_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3170_ = v___x_3146_;
v_isShared_3171_ = v_isSharedCheck_3178_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_val_3168_);
lean_dec(v___x_3146_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3178_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3172_ = l_Lean_LocalDecl_toExpr(v_val_3168_);
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v_projs_3118_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v___x_3173_);
v___x_3175_ = v___x_3170_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
return v___x_3176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3181_, lean_object* v_findLocalDecl_x3f_3182_, lean_object* v_n_3183_, lean_object* v_projs_3184_, lean_object* v_globalDeclFound_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
uint8_t v_globalDeclFound_boxed_3193_; lean_object* v_res_3194_; 
v_globalDeclFound_boxed_3193_ = lean_unbox(v_globalDeclFound_3185_);
v_res_3194_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3181_, v_findLocalDecl_x3f_3182_, v_n_3183_, v_projs_3184_, v_globalDeclFound_boxed_3193_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec_ref(v_view_3181_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3195_, lean_object* v_givenName_3196_, lean_object* v_as_3197_, lean_object* v_i_3198_){
_start:
{
lean_object* v_zero_3199_; uint8_t v_isZero_3200_; 
v_zero_3199_ = lean_unsigned_to_nat(0u);
v_isZero_3200_ = lean_nat_dec_eq(v_i_3198_, v_zero_3199_);
if (v_isZero_3200_ == 1)
{
lean_object* v___x_3201_; 
lean_dec(v_i_3198_);
v___x_3201_ = lean_box(0);
return v___x_3201_;
}
else
{
lean_object* v_one_3202_; lean_object* v_n_3203_; lean_object* v___y_3205_; lean_object* v___x_3207_; 
v_one_3202_ = lean_unsigned_to_nat(1u);
v_n_3203_ = lean_nat_sub(v_i_3198_, v_one_3202_);
lean_dec(v_i_3198_);
v___x_3207_ = lean_array_fget_borrowed(v_as_3197_, v_n_3203_);
if (lean_obj_tag(v___x_3207_) == 0)
{
v___y_3205_ = v___x_3207_;
goto v___jp_3204_;
}
else
{
lean_object* v_val_3208_; uint8_t v___x_3209_; 
v_val_3208_ = lean_ctor_get(v___x_3207_, 0);
v___x_3209_ = l_Lean_LocalDecl_isAuxDecl(v_val_3208_);
if (v___x_3209_ == 0)
{
v___y_3205_ = v_localDecl_x3f_3195_;
goto v___jp_3204_;
}
else
{
lean_object* v___x_3210_; uint8_t v___x_3211_; 
v___x_3210_ = l_Lean_LocalDecl_userName(v_val_3208_);
v___x_3211_ = lean_name_eq(v___x_3210_, v_givenName_3196_);
lean_dec(v___x_3210_);
if (v___x_3211_ == 0)
{
v_i_3198_ = v_n_3203_;
goto _start;
}
else
{
v___y_3205_ = v___x_3207_;
goto v___jp_3204_;
}
}
}
v___jp_3204_:
{
if (lean_obj_tag(v___y_3205_) == 0)
{
v_i_3198_ = v_n_3203_;
goto _start;
}
else
{
lean_dec(v_n_3203_);
lean_inc_ref(v___y_3205_);
return v___y_3205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3213_, lean_object* v_givenName_3214_, lean_object* v_as_3215_, lean_object* v_i_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3213_, v_givenName_3214_, v_as_3215_, v_i_3216_);
lean_dec_ref(v_as_3215_);
lean_dec(v_givenName_3214_);
lean_dec(v_localDecl_x3f_3213_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3218_, lean_object* v_givenName_3219_, lean_object* v_as_3220_, lean_object* v_i_3221_){
_start:
{
lean_object* v_zero_3222_; uint8_t v_isZero_3223_; 
v_zero_3222_ = lean_unsigned_to_nat(0u);
v_isZero_3223_ = lean_nat_dec_eq(v_i_3221_, v_zero_3222_);
if (v_isZero_3223_ == 1)
{
lean_object* v___x_3224_; 
lean_dec(v_i_3221_);
v___x_3224_ = lean_box(0);
return v___x_3224_;
}
else
{
lean_object* v_one_3225_; lean_object* v_n_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v_one_3225_ = lean_unsigned_to_nat(1u);
v_n_3226_ = lean_nat_sub(v_i_3221_, v_one_3225_);
lean_dec(v_i_3221_);
v___x_3227_ = lean_array_fget_borrowed(v_as_3220_, v_n_3226_);
v___x_3228_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3218_, v_givenName_3219_, v___x_3227_);
if (lean_obj_tag(v___x_3228_) == 0)
{
v_i_3221_ = v_n_3226_;
goto _start;
}
else
{
lean_dec(v_n_3226_);
return v___x_3228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3230_, lean_object* v_givenName_3231_, lean_object* v_x_3232_){
_start:
{
if (lean_obj_tag(v_x_3232_) == 0)
{
lean_object* v_cs_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_cs_3233_ = lean_ctor_get(v_x_3232_, 0);
v___x_3234_ = lean_array_get_size(v_cs_3233_);
v___x_3235_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3230_, v_givenName_3231_, v_cs_3233_, v___x_3234_);
return v___x_3235_;
}
else
{
lean_object* v_vs_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v_vs_3236_ = lean_ctor_get(v_x_3232_, 0);
v___x_3237_ = lean_array_get_size(v_vs_3236_);
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3230_, v_givenName_3231_, v_vs_3236_, v___x_3237_);
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3239_, lean_object* v_givenName_3240_, lean_object* v_x_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3239_, v_givenName_3240_, v_x_3241_);
lean_dec_ref(v_x_3241_);
lean_dec(v_givenName_3240_);
lean_dec(v_localDecl_x3f_3239_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3243_, lean_object* v_givenName_3244_, lean_object* v_as_3245_, lean_object* v_i_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3243_, v_givenName_3244_, v_as_3245_, v_i_3246_);
lean_dec_ref(v_as_3245_);
lean_dec(v_givenName_3244_);
lean_dec(v_localDecl_x3f_3243_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3248_, lean_object* v_givenName_3249_, lean_object* v_t_3250_){
_start:
{
lean_object* v_root_3251_; lean_object* v_tail_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_root_3251_ = lean_ctor_get(v_t_3250_, 0);
v_tail_3252_ = lean_ctor_get(v_t_3250_, 1);
v___x_3253_ = lean_array_get_size(v_tail_3252_);
v___x_3254_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3248_, v_givenName_3249_, v_tail_3252_, v___x_3253_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3248_, v_givenName_3249_, v_root_3251_);
return v___x_3255_;
}
else
{
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3256_, lean_object* v_givenName_3257_, lean_object* v_t_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3256_, v_givenName_3257_, v_t_3258_);
lean_dec_ref(v_t_3258_);
lean_dec(v_givenName_3257_);
lean_dec(v_localDecl_x3f_3256_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3260_, lean_object* v_k_3261_){
_start:
{
if (lean_obj_tag(v_t_3260_) == 0)
{
lean_object* v_k_3262_; lean_object* v_v_3263_; lean_object* v_l_3264_; lean_object* v_r_3265_; uint8_t v___x_3266_; 
v_k_3262_ = lean_ctor_get(v_t_3260_, 1);
v_v_3263_ = lean_ctor_get(v_t_3260_, 2);
v_l_3264_ = lean_ctor_get(v_t_3260_, 3);
v_r_3265_ = lean_ctor_get(v_t_3260_, 4);
v___x_3266_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3261_, v_k_3262_);
switch(v___x_3266_)
{
case 0:
{
v_t_3260_ = v_l_3264_;
goto _start;
}
case 1:
{
lean_object* v___x_3268_; 
lean_inc(v_v_3263_);
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_v_3263_);
return v___x_3268_;
}
default: 
{
v_t_3260_ = v_r_3265_;
goto _start;
}
}
}
else
{
lean_object* v___x_3270_; 
v___x_3270_ = lean_box(0);
return v___x_3270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3271_, lean_object* v_k_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3271_, v_k_3272_);
lean_dec(v_k_3272_);
lean_dec(v_t_3271_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3274_, lean_object* v_givenName_3275_){
_start:
{
lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = l_Lean_LocalDecl_userName(v_localDecl_3274_);
v___x_3277_ = lean_name_eq(v___x_3276_, v_givenName_3275_);
lean_dec(v___x_3276_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; 
lean_dec_ref(v_localDecl_3274_);
v___x_3278_ = lean_box(0);
return v___x_3278_;
}
else
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3279_, 0, v_localDecl_3274_);
return v___x_3279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3280_, lean_object* v_givenName_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3280_, v_givenName_3281_);
lean_dec(v_givenName_3281_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3283_, uint8_t v_skipAuxDecl_3284_, lean_object* v_auxDeclToFullName_3285_, lean_object* v___x_3286_, lean_object* v_givenNameView_3287_, lean_object* v_as_3288_, lean_object* v_i_3289_){
_start:
{
lean_object* v_zero_3290_; uint8_t v_isZero_3291_; 
v_zero_3290_ = lean_unsigned_to_nat(0u);
v_isZero_3291_ = lean_nat_dec_eq(v_i_3289_, v_zero_3290_);
if (v_isZero_3291_ == 1)
{
lean_object* v___x_3292_; 
lean_dec(v_i_3289_);
lean_dec_ref(v_givenNameView_3287_);
lean_dec(v___x_3286_);
v___x_3292_ = lean_box(0);
return v___x_3292_;
}
else
{
lean_object* v_one_3293_; lean_object* v_n_3294_; lean_object* v___y_3296_; lean_object* v___x_3298_; 
v_one_3293_ = lean_unsigned_to_nat(1u);
v_n_3294_ = lean_nat_sub(v_i_3289_, v_one_3293_);
lean_dec(v_i_3289_);
v___x_3298_ = lean_array_fget_borrowed(v_as_3288_, v_n_3294_);
if (lean_obj_tag(v___x_3298_) == 0)
{
v___y_3296_ = v___x_3298_;
goto v___jp_3295_;
}
else
{
lean_object* v_val_3299_; uint8_t v___x_3300_; 
v_val_3299_ = lean_ctor_get(v___x_3298_, 0);
v___x_3300_ = l_Lean_LocalDecl_isAuxDecl(v_val_3299_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; 
lean_inc(v_val_3299_);
v___x_3301_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3299_, v_givenName_3283_);
v___y_3296_ = v___x_3301_;
goto v___jp_3295_;
}
else
{
if (v_skipAuxDecl_3284_ == 0)
{
if (v___x_3300_ == 0)
{
v_i_3289_ = v_n_3294_;
goto _start;
}
else
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = l_Lean_LocalDecl_fvarId(v_val_3299_);
v___x_3304_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3285_, v___x_3303_);
lean_dec(v___x_3303_);
if (lean_obj_tag(v___x_3304_) == 1)
{
lean_object* v_val_3305_; lean_object* v_fullDeclView_3306_; lean_object* v___y_3308_; lean_object* v_name_3329_; lean_object* v___x_3330_; 
v_val_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_val_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v_fullDeclView_3306_ = l_Lean_extractMacroScopes(v_val_3305_);
v_name_3329_ = lean_ctor_get(v_fullDeclView_3306_, 0);
lean_inc(v_name_3329_);
v___x_3330_ = l_Lean_privateToUserName_x3f(v_name_3329_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_inc(v_name_3329_);
v___y_3308_ = v_name_3329_;
goto v___jp_3307_;
}
else
{
lean_object* v_val_3331_; 
v_val_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_val_3331_);
lean_dec_ref_known(v___x_3330_, 1);
v___y_3308_ = v_val_3331_;
goto v___jp_3307_;
}
v___jp_3307_:
{
lean_object* v_imported_3309_; lean_object* v_ctx_3310_; lean_object* v_scopes_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3327_; 
v_imported_3309_ = lean_ctor_get(v_fullDeclView_3306_, 1);
v_ctx_3310_ = lean_ctor_get(v_fullDeclView_3306_, 2);
v_scopes_3311_ = lean_ctor_get(v_fullDeclView_3306_, 3);
v_isSharedCheck_3327_ = !lean_is_exclusive(v_fullDeclView_3306_);
if (v_isSharedCheck_3327_ == 0)
{
lean_object* v_unused_3328_; 
v_unused_3328_ = lean_ctor_get(v_fullDeclView_3306_, 0);
lean_dec(v_unused_3328_);
v___x_3313_ = v_fullDeclView_3306_;
v_isShared_3314_ = v_isSharedCheck_3327_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_scopes_3311_);
lean_inc(v_ctx_3310_);
lean_inc(v_imported_3309_);
lean_dec(v_fullDeclView_3306_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3327_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v_fullDeclView_3316_; 
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v___y_3308_);
v_fullDeclView_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___y_3308_);
lean_ctor_set(v_reuseFailAlloc_3326_, 1, v_imported_3309_);
lean_ctor_set(v_reuseFailAlloc_3326_, 2, v_ctx_3310_);
lean_ctor_set(v_reuseFailAlloc_3326_, 3, v_scopes_3311_);
v_fullDeclView_3316_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v_fullDeclName_3317_; uint8_t v___x_3318_; 
lean_inc_ref(v_fullDeclView_3316_);
v_fullDeclName_3317_ = l_Lean_MacroScopesView_review(v_fullDeclView_3316_);
v___x_3318_ = l_Lean_Name_isPrefixOf(v___x_3286_, v_fullDeclName_3317_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; 
lean_dec_ref(v_fullDeclView_3316_);
lean_inc(v___x_3286_);
lean_inc_ref(v_givenNameView_3287_);
lean_inc(v_val_3299_);
v___x_3319_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3299_, v_givenNameView_3287_, v_fullDeclName_3317_, v___x_3286_);
lean_dec(v_fullDeclName_3317_);
v___y_3296_ = v___x_3319_;
goto v___jp_3295_;
}
else
{
lean_object* v___x_3320_; lean_object* v_localDeclNameView_3321_; uint8_t v___x_3322_; 
lean_dec(v_fullDeclName_3317_);
v___x_3320_ = l_Lean_LocalDecl_userName(v_val_3299_);
v_localDeclNameView_3321_ = l_Lean_extractMacroScopes(v___x_3320_);
v___x_3322_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3321_, v_givenNameView_3287_);
lean_dec_ref(v_localDeclNameView_3321_);
if (v___x_3322_ == 0)
{
lean_dec_ref(v_fullDeclView_3316_);
v_i_3289_ = v_n_3294_;
goto _start;
}
else
{
uint8_t v___x_3324_; 
v___x_3324_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3287_, v_fullDeclView_3316_);
lean_dec_ref(v_fullDeclView_3316_);
if (v___x_3324_ == 0)
{
v_i_3289_ = v_n_3294_;
goto _start;
}
else
{
lean_inc_ref(v___x_3298_);
v___y_3296_ = v___x_3298_;
goto v___jp_3295_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3332_; 
lean_dec(v___x_3304_);
lean_inc(v_val_3299_);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3299_, v_givenName_3283_);
v___y_3296_ = v___x_3332_;
goto v___jp_3295_;
}
}
}
else
{
v_i_3289_ = v_n_3294_;
goto _start;
}
}
}
v___jp_3295_:
{
if (lean_obj_tag(v___y_3296_) == 0)
{
v_i_3289_ = v_n_3294_;
goto _start;
}
else
{
lean_dec(v_n_3294_);
lean_dec_ref(v_givenNameView_3287_);
lean_dec(v___x_3286_);
return v___y_3296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3334_, lean_object* v_skipAuxDecl_3335_, lean_object* v_auxDeclToFullName_3336_, lean_object* v___x_3337_, lean_object* v_givenNameView_3338_, lean_object* v_as_3339_, lean_object* v_i_3340_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3341_; lean_object* v_res_3342_; 
v_skipAuxDecl_boxed_3341_ = lean_unbox(v_skipAuxDecl_3335_);
v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3334_, v_skipAuxDecl_boxed_3341_, v_auxDeclToFullName_3336_, v___x_3337_, v_givenNameView_3338_, v_as_3339_, v_i_3340_);
lean_dec_ref(v_as_3339_);
lean_dec(v_auxDeclToFullName_3336_);
lean_dec(v_givenName_3334_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3343_, uint8_t v_skipAuxDecl_3344_, lean_object* v_auxDeclToFullName_3345_, lean_object* v___x_3346_, lean_object* v_givenNameView_3347_, lean_object* v_as_3348_, lean_object* v_i_3349_){
_start:
{
lean_object* v_zero_3350_; uint8_t v_isZero_3351_; 
v_zero_3350_ = lean_unsigned_to_nat(0u);
v_isZero_3351_ = lean_nat_dec_eq(v_i_3349_, v_zero_3350_);
if (v_isZero_3351_ == 1)
{
lean_object* v___x_3352_; 
lean_dec(v_i_3349_);
lean_dec_ref(v_givenNameView_3347_);
lean_dec(v___x_3346_);
v___x_3352_ = lean_box(0);
return v___x_3352_;
}
else
{
lean_object* v_one_3353_; lean_object* v_n_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_one_3353_ = lean_unsigned_to_nat(1u);
v_n_3354_ = lean_nat_sub(v_i_3349_, v_one_3353_);
lean_dec(v_i_3349_);
v___x_3355_ = lean_array_fget_borrowed(v_as_3348_, v_n_3354_);
lean_inc_ref(v_givenNameView_3347_);
lean_inc(v___x_3346_);
v___x_3356_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3343_, v_skipAuxDecl_3344_, v_auxDeclToFullName_3345_, v___x_3346_, v_givenNameView_3347_, v___x_3355_);
if (lean_obj_tag(v___x_3356_) == 0)
{
v_i_3349_ = v_n_3354_;
goto _start;
}
else
{
lean_dec(v_n_3354_);
lean_dec_ref(v_givenNameView_3347_);
lean_dec(v___x_3346_);
return v___x_3356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3358_, uint8_t v_skipAuxDecl_3359_, lean_object* v_auxDeclToFullName_3360_, lean_object* v___x_3361_, lean_object* v_givenNameView_3362_, lean_object* v_x_3363_){
_start:
{
if (lean_obj_tag(v_x_3363_) == 0)
{
lean_object* v_cs_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_cs_3364_ = lean_ctor_get(v_x_3363_, 0);
v___x_3365_ = lean_array_get_size(v_cs_3364_);
v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3358_, v_skipAuxDecl_3359_, v_auxDeclToFullName_3360_, v___x_3361_, v_givenNameView_3362_, v_cs_3364_, v___x_3365_);
return v___x_3366_;
}
else
{
lean_object* v_vs_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v_vs_3367_ = lean_ctor_get(v_x_3363_, 0);
v___x_3368_ = lean_array_get_size(v_vs_3367_);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3358_, v_skipAuxDecl_3359_, v_auxDeclToFullName_3360_, v___x_3361_, v_givenNameView_3362_, v_vs_3367_, v___x_3368_);
return v___x_3369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3370_, lean_object* v_skipAuxDecl_3371_, lean_object* v_auxDeclToFullName_3372_, lean_object* v___x_3373_, lean_object* v_givenNameView_3374_, lean_object* v_x_3375_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3376_; lean_object* v_res_3377_; 
v_skipAuxDecl_boxed_3376_ = lean_unbox(v_skipAuxDecl_3371_);
v_res_3377_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3370_, v_skipAuxDecl_boxed_3376_, v_auxDeclToFullName_3372_, v___x_3373_, v_givenNameView_3374_, v_x_3375_);
lean_dec_ref(v_x_3375_);
lean_dec(v_auxDeclToFullName_3372_);
lean_dec(v_givenName_3370_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3378_, lean_object* v_skipAuxDecl_3379_, lean_object* v_auxDeclToFullName_3380_, lean_object* v___x_3381_, lean_object* v_givenNameView_3382_, lean_object* v_as_3383_, lean_object* v_i_3384_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3385_; lean_object* v_res_3386_; 
v_skipAuxDecl_boxed_3385_ = lean_unbox(v_skipAuxDecl_3379_);
v_res_3386_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3378_, v_skipAuxDecl_boxed_3385_, v_auxDeclToFullName_3380_, v___x_3381_, v_givenNameView_3382_, v_as_3383_, v_i_3384_);
lean_dec_ref(v_as_3383_);
lean_dec(v_auxDeclToFullName_3380_);
lean_dec(v_givenName_3378_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3387_, uint8_t v_skipAuxDecl_3388_, lean_object* v_auxDeclToFullName_3389_, lean_object* v___x_3390_, lean_object* v_givenNameView_3391_, lean_object* v_t_3392_){
_start:
{
lean_object* v_root_3393_; lean_object* v_tail_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v_root_3393_ = lean_ctor_get(v_t_3392_, 0);
v_tail_3394_ = lean_ctor_get(v_t_3392_, 1);
v___x_3395_ = lean_array_get_size(v_tail_3394_);
lean_inc_ref(v_givenNameView_3391_);
lean_inc(v___x_3390_);
v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3387_, v_skipAuxDecl_3388_, v_auxDeclToFullName_3389_, v___x_3390_, v_givenNameView_3391_, v_tail_3394_, v___x_3395_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3387_, v_skipAuxDecl_3388_, v_auxDeclToFullName_3389_, v___x_3390_, v_givenNameView_3391_, v_root_3393_);
return v___x_3397_;
}
else
{
lean_dec_ref(v_givenNameView_3391_);
lean_dec(v___x_3390_);
return v___x_3396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3398_, lean_object* v_skipAuxDecl_3399_, lean_object* v_auxDeclToFullName_3400_, lean_object* v___x_3401_, lean_object* v_givenNameView_3402_, lean_object* v_t_3403_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3404_; lean_object* v_res_3405_; 
v_skipAuxDecl_boxed_3404_ = lean_unbox(v_skipAuxDecl_3399_);
v_res_3405_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3398_, v_skipAuxDecl_boxed_3404_, v_auxDeclToFullName_3400_, v___x_3401_, v_givenNameView_3402_, v_t_3403_);
lean_dec_ref(v_t_3403_);
lean_dec(v_auxDeclToFullName_3400_);
lean_dec(v_givenName_3398_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3406_, lean_object* v_currNamespace_3407_, lean_object* v_decls_3408_, lean_object* v_givenNameView_3409_, uint8_t v_skipAuxDecl_3410_){
_start:
{
lean_object* v_givenName_3411_; lean_object* v_localDecl_x3f_3412_; 
lean_inc_ref(v_givenNameView_3409_);
v_givenName_3411_ = l_Lean_MacroScopesView_review(v_givenNameView_3409_);
v_localDecl_x3f_3412_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3411_, v_skipAuxDecl_3410_, v_auxDeclToFullName_3406_, v_currNamespace_3407_, v_givenNameView_3409_, v_decls_3408_);
if (lean_obj_tag(v_localDecl_x3f_3412_) == 0)
{
if (v_skipAuxDecl_3410_ == 0)
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3412_, v_givenName_3411_, v_decls_3408_);
lean_dec(v_givenName_3411_);
return v___x_3413_;
}
else
{
lean_dec(v_givenName_3411_);
return v_localDecl_x3f_3412_;
}
}
else
{
lean_dec(v_givenName_3411_);
return v_localDecl_x3f_3412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3414_, lean_object* v_currNamespace_3415_, lean_object* v_decls_3416_, lean_object* v_givenNameView_3417_, lean_object* v_skipAuxDecl_3418_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3419_; lean_object* v_res_3420_; 
v_skipAuxDecl_boxed_3419_ = lean_unbox(v_skipAuxDecl_3418_);
v_res_3420_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3414_, v_currNamespace_3415_, v_decls_3416_, v_givenNameView_3417_, v_skipAuxDecl_boxed_3419_);
lean_dec_ref(v_decls_3416_);
lean_dec(v_auxDeclToFullName_3414_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_lctx_3429_; lean_object* v_toCold_3430_; lean_object* v_decls_3431_; lean_object* v_auxDeclToFullName_3432_; lean_object* v_currNamespace_3433_; lean_object* v_view_3434_; lean_object* v_name_3435_; lean_object* v_findLocalDecl_x3f_3436_; lean_object* v___x_3437_; uint8_t v___x_3438_; lean_object* v___x_3439_; 
v_lctx_3429_ = lean_ctor_get(v___y_3424_, 2);
v_toCold_3430_ = lean_ctor_get(v___y_3426_, 0);
v_decls_3431_ = lean_ctor_get(v_lctx_3429_, 1);
v_auxDeclToFullName_3432_ = lean_ctor_get(v_lctx_3429_, 2);
v_currNamespace_3433_ = lean_ctor_get(v_toCold_3430_, 4);
v_view_3434_ = l_Lean_extractMacroScopes(v_n_3421_);
v_name_3435_ = lean_ctor_get(v_view_3434_, 0);
lean_inc(v_name_3435_);
lean_inc_ref(v_decls_3431_);
lean_inc(v_currNamespace_3433_);
lean_inc(v_auxDeclToFullName_3432_);
v_findLocalDecl_x3f_3436_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3436_, 0, v_auxDeclToFullName_3432_);
lean_closure_set(v_findLocalDecl_x3f_3436_, 1, v_currNamespace_3433_);
lean_closure_set(v_findLocalDecl_x3f_3436_, 2, v_decls_3431_);
v___x_3437_ = lean_box(0);
v___x_3438_ = 0;
v___x_3439_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3434_, v_findLocalDecl_x3f_3436_, v_name_3435_, v___x_3437_, v___x_3438_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec_ref(v_view_3434_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3449_, lean_object* v_b_3450_){
_start:
{
if (lean_obj_tag(v_as_x27_3449_) == 0)
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v_b_3450_);
return v___x_3452_;
}
else
{
lean_object* v_head_3453_; lean_object* v_tail_3454_; lean_object* v_config_3455_; lean_object* v_extensions_3456_; lean_object* v_extra_3457_; lean_object* v_extraInj_3458_; lean_object* v_extraFacts_3459_; lean_object* v_symPrios_3460_; lean_object* v_norm_3461_; lean_object* v_normProcs_3462_; lean_object* v_anchorRefs_x3f_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3472_; 
v_head_3453_ = lean_ctor_get(v_as_x27_3449_, 0);
v_tail_3454_ = lean_ctor_get(v_as_x27_3449_, 1);
v_config_3455_ = lean_ctor_get(v_b_3450_, 0);
v_extensions_3456_ = lean_ctor_get(v_b_3450_, 1);
v_extra_3457_ = lean_ctor_get(v_b_3450_, 2);
v_extraInj_3458_ = lean_ctor_get(v_b_3450_, 3);
v_extraFacts_3459_ = lean_ctor_get(v_b_3450_, 4);
v_symPrios_3460_ = lean_ctor_get(v_b_3450_, 5);
v_norm_3461_ = lean_ctor_get(v_b_3450_, 6);
v_normProcs_3462_ = lean_ctor_get(v_b_3450_, 7);
v_anchorRefs_x3f_3463_ = lean_ctor_get(v_b_3450_, 8);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_b_3450_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3465_ = v_b_3450_;
v_isShared_3466_ = v_isSharedCheck_3472_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_anchorRefs_x3f_3463_);
lean_inc(v_normProcs_3462_);
lean_inc(v_norm_3461_);
lean_inc(v_symPrios_3460_);
lean_inc(v_extraFacts_3459_);
lean_inc(v_extraInj_3458_);
lean_inc(v_extra_3457_);
lean_inc(v_extensions_3456_);
lean_inc(v_config_3455_);
lean_dec(v_b_3450_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3472_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
lean_inc(v_head_3453_);
v___x_3467_ = l_Lean_PersistentArray_push___redArg(v_extra_3457_, v_head_3453_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 2, v___x_3467_);
v___x_3469_ = v___x_3465_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_config_3455_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_extensions_3456_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v___x_3467_);
lean_ctor_set(v_reuseFailAlloc_3471_, 3, v_extraInj_3458_);
lean_ctor_set(v_reuseFailAlloc_3471_, 4, v_extraFacts_3459_);
lean_ctor_set(v_reuseFailAlloc_3471_, 5, v_symPrios_3460_);
lean_ctor_set(v_reuseFailAlloc_3471_, 6, v_norm_3461_);
lean_ctor_set(v_reuseFailAlloc_3471_, 7, v_normProcs_3462_);
lean_ctor_set(v_reuseFailAlloc_3471_, 8, v_anchorRefs_x3f_3463_);
v___x_3469_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
v_as_x27_3449_ = v_tail_3454_;
v_b_3450_ = v___x_3469_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3473_, lean_object* v_b_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3473_, v_b_3474_);
lean_dec(v_as_x27_3473_);
return v_res_3476_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3479_ = l_Lean_stringToMessageData(v___x_3478_);
return v___x_3479_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3482_ = l_Lean_stringToMessageData(v___x_3481_);
return v___x_3482_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3485_ = l_Lean_stringToMessageData(v___x_3484_);
return v___x_3485_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3488_ = l_Lean_stringToMessageData(v___x_3487_);
return v___x_3488_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3491_ = l_Lean_stringToMessageData(v___x_3490_);
return v___x_3491_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3494_ = l_Lean_stringToMessageData(v___x_3493_);
return v___x_3494_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3497_ = l_Lean_stringToMessageData(v___x_3496_);
return v___x_3497_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3500_ = l_Lean_stringToMessageData(v___x_3499_);
return v___x_3500_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3503_ = l_Lean_stringToMessageData(v___x_3502_);
return v___x_3503_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3506_ = l_Lean_stringToMessageData(v___x_3505_);
return v___x_3506_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3509_ = l_Lean_stringToMessageData(v___x_3508_);
return v___x_3509_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22));
v___x_3512_ = l_Lean_stringToMessageData(v___x_3511_);
return v___x_3512_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24));
v___x_3515_ = l_Lean_stringToMessageData(v___x_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3516_, lean_object* v_p_3517_, lean_object* v_mod_x3f_3518_, lean_object* v_id_3519_, uint8_t v_minIndexable_3520_, uint8_t v_only_3521_, uint8_t v_incremental_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_){
_start:
{
uint8_t v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3633_; uint8_t v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v_a_3685_; lean_object* v___y_3910_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3921_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3922_ = lean_box(0);
lean_inc(v_id_3519_);
v___x_3923_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3519_, v___x_3922_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v_a_3685_ = v_a_3924_;
goto v___jp_3684_;
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3999_; 
v_a_3925_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3927_ = v___x_3923_;
v_isShared_3928_ = v_isSharedCheck_3999_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3923_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3999_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
uint8_t v___y_3930_; uint8_t v___x_3997_; 
v___x_3997_ = l_Lean_Exception_isInterrupt(v_a_3925_);
if (v___x_3997_ == 0)
{
uint8_t v___x_3998_; 
lean_inc(v_a_3925_);
v___x_3998_ = l_Lean_Exception_isRuntime(v_a_3925_);
v___y_3930_ = v___x_3998_;
goto v___jp_3929_;
}
else
{
v___y_3930_ = v___x_3997_;
goto v___jp_3929_;
}
v___jp_3929_:
{
if (v___y_3930_ == 0)
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_del_object(v___x_3927_);
v___x_3931_ = l_Lean_TSyntax_getId(v_id_3519_);
lean_inc(v___x_3931_);
v___x_3932_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_3931_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_a_3933_);
lean_dec_ref_known(v___x_3932_, 1);
if (lean_obj_tag(v_a_3933_) == 0)
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_3931_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3963_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3937_ = v___x_3934_;
v_isShared_3938_ = v_isSharedCheck_3963_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3963_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
if (lean_obj_tag(v_a_3935_) == 1)
{
lean_del_object(v___x_3937_);
lean_dec(v_a_3925_);
if (lean_obj_tag(v_mod_x3f_3518_) == 1)
{
lean_object* v_val_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec_ref_known(v_a_3935_, 1);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_val_3939_ = lean_ctor_get(v_mod_x3f_3518_, 0);
lean_inc(v_val_3939_);
lean_dec_ref_known(v_mod_x3f_3518_, 1);
v___x_3940_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_3941_ = l_Lean_MessageData_ofName(v___x_3931_);
v___x_3942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3940_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_3944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3942_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
v___x_3945_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_3939_, v___x_3944_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
lean_dec(v_val_3939_);
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3945_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3945_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
else
{
lean_object* v_val_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
lean_dec(v___x_3931_);
v_val_3954_ = lean_ctor_get(v_a_3935_, 0);
lean_inc(v_val_3954_);
lean_dec_ref_known(v_a_3935_, 1);
v___x_3955_ = lean_box(0);
lean_inc_ref(v_params_3516_);
v___x_3956_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3516_, v_val_3954_, v___x_3921_, v___x_3955_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
lean_dec(v_val_3954_);
v___y_3910_ = v___x_3956_;
goto v___jp_3909_;
}
}
else
{
lean_object* v___x_3957_; uint8_t v___x_3958_; 
lean_dec(v_a_3935_);
v___x_3957_ = l_Lean_Name_getPrefix(v___x_3931_);
lean_dec(v___x_3931_);
v___x_3958_ = l_Lean_Name_isAnonymous(v___x_3957_);
lean_dec(v___x_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; 
lean_del_object(v___x_3937_);
lean_dec(v_a_3925_);
v___x_3959_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3516_, v_p_3517_, v_mod_x3f_3518_, v_id_3519_, v_minIndexable_3520_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
return v___x_3959_;
}
else
{
lean_object* v___x_3961_; 
lean_dec(v_id_3519_);
lean_dec(v_mod_x3f_3518_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set_tag(v___x_3937_, 1);
lean_ctor_set(v___x_3937_, 0, v_a_3925_);
v___x_3961_ = v___x_3937_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3925_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec(v___x_3931_);
lean_dec(v_a_3925_);
lean_dec(v_id_3519_);
lean_dec(v_mod_x3f_3518_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_a_3964_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3934_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3934_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
else
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec_ref_known(v_a_3933_, 1);
lean_dec(v___x_3931_);
lean_dec(v_a_3925_);
lean_dec(v_mod_x3f_3518_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v___x_3972_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23);
lean_inc(v_id_3519_);
v___x_3973_ = l_Lean_MessageData_ofSyntax(v_id_3519_);
v___x_3974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3972_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25);
v___x_3976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3974_);
lean_ctor_set(v___x_3976_, 1, v___x_3975_);
v___x_3977_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3519_, v___x_3976_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
lean_dec(v_id_3519_);
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3977_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3977_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_dec(v___x_3931_);
lean_dec(v_a_3925_);
lean_dec(v_id_3519_);
lean_dec(v_mod_x3f_3518_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_a_3986_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3932_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3932_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
else
{
lean_object* v___x_3995_; 
lean_dec(v_id_3519_);
lean_dec(v_mod_x3f_3518_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
if (v_isShared_3928_ == 0)
{
v___x_3995_ = v___x_3927_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3925_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
v___jp_3530_:
{
uint8_t v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = 0;
lean_inc(v___y_3532_);
v___x_3540_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3532_, v___x_3539_, v___y_3537_, v___y_3538_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3540_, 1);
if (lean_obj_tag(v_a_3541_) == 1)
{
lean_object* v_val_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
lean_dec(v___y_3532_);
v_val_3542_ = lean_ctor_get(v_a_3541_, 0);
lean_inc_n(v_val_3542_, 2);
lean_dec_ref_known(v_a_3541_, 1);
v___x_3543_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3516_, v_val_3542_, v___x_3539_);
v___x_3544_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3542_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3555_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3555_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3555_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
if (lean_obj_tag(v_a_3545_) == 1)
{
lean_object* v_val_3549_; lean_object* v_ctors_3550_; lean_object* v___x_3551_; 
lean_del_object(v___x_3547_);
v_val_3549_ = lean_ctor_get(v_a_3545_, 0);
lean_inc(v_val_3549_);
lean_dec_ref_known(v_a_3545_, 1);
v_ctors_3550_ = lean_ctor_get(v_val_3549_, 4);
lean_inc(v_ctors_3550_);
lean_dec(v_val_3549_);
v___x_3551_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3517_, v_id_3519_, v_minIndexable_3520_, v_ctors_3550_, v___x_3543_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v_ctors_3550_);
lean_dec(v_p_3517_);
return v___x_3551_;
}
else
{
lean_object* v___x_3553_; 
lean_dec(v_a_3545_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3543_);
v___x_3553_ = v___x_3547_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3543_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec_ref(v___x_3543_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
v_a_3556_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3544_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3544_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
else
{
lean_object* v_toCold_3564_; lean_object* v_currRecDepth_3565_; lean_object* v_ref_3566_; uint16_t v_optionFlags_3567_; uint8_t v_suppressElabErrors_3568_; uint8_t v_isRecordingDeps_3569_; lean_object* v___x_3570_; lean_object* v_ref_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec(v_a_3541_);
v_toCold_3564_ = lean_ctor_get(v___y_3537_, 0);
v_currRecDepth_3565_ = lean_ctor_get(v___y_3537_, 1);
v_ref_3566_ = lean_ctor_get(v___y_3537_, 2);
v_optionFlags_3567_ = lean_ctor_get_uint16(v___y_3537_, sizeof(void*)*3);
v_suppressElabErrors_3568_ = lean_ctor_get_uint8(v___y_3537_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3569_ = lean_ctor_get_uint8(v___y_3537_, sizeof(void*)*3 + 3);
v___x_3570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_3571_ = l_Lean_replaceRef(v_p_3517_, v_ref_3566_);
lean_dec(v_p_3517_);
lean_inc(v_currRecDepth_3565_);
lean_inc_ref(v_toCold_3564_);
v___x_3572_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3572_, 0, v_toCold_3564_);
lean_ctor_set(v___x_3572_, 1, v_currRecDepth_3565_);
lean_ctor_set(v___x_3572_, 2, v_ref_3571_);
lean_ctor_set_uint16(v___x_3572_, sizeof(void*)*3, v_optionFlags_3567_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*3 + 2, v_suppressElabErrors_3568_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*3 + 3, v_isRecordingDeps_3569_);
v___x_3573_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3516_, v_id_3519_, v___y_3532_, v___x_3570_, v_minIndexable_3520_, v___y_3531_, v___y_3531_, v___y_3535_, v___y_3536_, v___x_3572_, v___y_3538_);
lean_dec_ref_known(v___x_3572_, 3);
return v___x_3573_;
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec(v___y_3532_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_a_3574_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3540_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3540_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
v___jp_3582_:
{
lean_object* v___x_3591_; 
v___x_3591_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3520_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_dec_ref_known(v___x_3591_, 1);
v___x_3592_ = l_Lean_Meta_Grind_grindExt;
v___x_3593_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3592_, v___y_3590_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref_known(v___x_3593_, 1);
lean_inc(v___y_3584_);
v___x_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3595_, 0, v___y_3584_);
v___x_3596_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3594_, v___x_3595_);
lean_dec_ref_known(v___x_3595_, 1);
lean_dec(v_a_3594_);
v___x_3597_ = lean_box(0);
v___x_3598_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3583_, v___x_3596_, v___x_3597_);
lean_dec(v___y_3583_);
v___x_3599_ = l_List_isEmpty___redArg(v___x_3598_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; 
lean_dec(v___y_3584_);
lean_dec(v_p_3517_);
v___x_3600_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3598_, v_params_3516_);
lean_dec(v___x_3598_);
return v___x_3600_;
}
else
{
lean_object* v___x_3601_; uint8_t v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec(v___x_3598_);
lean_dec_ref(v_params_3516_);
v___x_3601_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3602_ = 0;
v___x_3603_ = l_Lean_MessageData_ofConstName(v___y_3584_, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3601_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3604_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3517_, v___x_3606_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v_p_3517_);
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3607_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_a_3616_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3593_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3593_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_a_3624_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3591_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3591_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
v___jp_3632_:
{
lean_object* v___x_3639_; 
v___x_3639_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3520_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_toCold_3640_; lean_object* v_currRecDepth_3641_; lean_object* v_ref_3642_; uint16_t v_optionFlags_3643_; uint8_t v_suppressElabErrors_3644_; uint8_t v_isRecordingDeps_3645_; lean_object* v_ref_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
lean_dec_ref_known(v___x_3639_, 1);
v_toCold_3640_ = lean_ctor_get(v___y_3637_, 0);
v_currRecDepth_3641_ = lean_ctor_get(v___y_3637_, 1);
v_ref_3642_ = lean_ctor_get(v___y_3637_, 2);
v_optionFlags_3643_ = lean_ctor_get_uint16(v___y_3637_, sizeof(void*)*3);
v_suppressElabErrors_3644_ = lean_ctor_get_uint8(v___y_3637_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3645_ = lean_ctor_get_uint8(v___y_3637_, sizeof(void*)*3 + 3);
v_ref_3646_ = l_Lean_replaceRef(v_p_3517_, v_ref_3642_);
lean_dec(v_p_3517_);
lean_inc(v_currRecDepth_3641_);
lean_inc_ref(v_toCold_3640_);
v___x_3647_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3647_, 0, v_toCold_3640_);
lean_ctor_set(v___x_3647_, 1, v_currRecDepth_3641_);
lean_ctor_set(v___x_3647_, 2, v_ref_3646_);
lean_ctor_set_uint16(v___x_3647_, sizeof(void*)*3, v_optionFlags_3643_);
lean_ctor_set_uint8(v___x_3647_, sizeof(void*)*3 + 2, v_suppressElabErrors_3644_);
lean_ctor_set_uint8(v___x_3647_, sizeof(void*)*3 + 3, v_isRecordingDeps_3645_);
lean_inc(v___y_3633_);
v___x_3648_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3633_, v___y_3634_, v___x_3647_, v___y_3638_);
lean_dec_ref_known(v___x_3647_, 3);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3656_; 
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3656_ == 0)
{
lean_object* v_unused_3657_; 
v_unused_3657_ = lean_ctor_get(v___x_3648_, 0);
lean_dec(v_unused_3657_);
v___x_3650_ = v___x_3648_;
v_isShared_3651_ = v_isSharedCheck_3656_;
goto v_resetjp_3649_;
}
else
{
lean_dec(v___x_3648_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3656_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; lean_object* v___x_3654_; 
v___x_3652_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3516_, v___y_3633_, v___y_3634_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3652_);
v___x_3654_ = v___x_3650_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec(v___y_3633_);
lean_dec_ref(v_params_3516_);
v_a_3658_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3648_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3648_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec(v___y_3633_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_a_3666_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3639_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3639_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
v___jp_3674_:
{
lean_object* v_ctors_3682_; lean_object* v___x_3683_; 
v_ctors_3682_ = lean_ctor_get(v___y_3675_, 4);
lean_inc(v_ctors_3682_);
lean_dec_ref(v___y_3675_);
v___x_3683_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3517_, v_id_3519_, v_minIndexable_3520_, v_ctors_3682_, v_params_3516_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
lean_dec(v_ctors_3682_);
lean_dec(v_p_3517_);
return v___x_3683_;
}
v___jp_3684_:
{
uint8_t v___x_3686_; lean_object* v___x_3687_; 
v___x_3686_ = 1;
lean_inc(v_a_3685_);
v___x_3687_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_3685_, v___x_3686_, v_a_3523_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_dec_ref_known(v___x_3687_, 1);
if (lean_obj_tag(v_mod_x3f_3518_) == 1)
{
lean_object* v_val_3688_; lean_object* v___x_3689_; 
v_val_3688_ = lean_ctor_get(v_mod_x3f_3518_, 0);
lean_inc(v_val_3688_);
lean_dec_ref_known(v_mod_x3f_3518_, 1);
v___x_3689_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3688_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3892_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3892_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3892_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
switch(lean_obj_tag(v_a_3690_))
{
case 0:
{
lean_object* v_k_3694_; 
lean_del_object(v___x_3692_);
v_k_3694_ = lean_ctor_get(v_a_3690_, 0);
lean_inc(v_k_3694_);
lean_dec_ref_known(v_a_3690_, 1);
if (lean_obj_tag(v_k_3694_) == 9)
{
lean_dec(v_id_3519_);
if (v_only_3521_ == 0)
{
lean_object* v_toCold_3695_; lean_object* v_currRecDepth_3696_; lean_object* v_ref_3697_; uint16_t v_optionFlags_3698_; uint8_t v_suppressElabErrors_3699_; uint8_t v_isRecordingDeps_3700_; lean_object* v_ref_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v_toCold_3695_ = lean_ctor_get(v_a_3527_, 0);
v_currRecDepth_3696_ = lean_ctor_get(v_a_3527_, 1);
v_ref_3697_ = lean_ctor_get(v_a_3527_, 2);
v_optionFlags_3698_ = lean_ctor_get_uint16(v_a_3527_, sizeof(void*)*3);
v_suppressElabErrors_3699_ = lean_ctor_get_uint8(v_a_3527_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3700_ = lean_ctor_get_uint8(v_a_3527_, sizeof(void*)*3 + 3);
v_ref_3701_ = l_Lean_replaceRef(v_p_3517_, v_ref_3697_);
lean_inc(v_currRecDepth_3696_);
lean_inc_ref(v_toCold_3695_);
v___x_3702_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3702_, 0, v_toCold_3695_);
lean_ctor_set(v___x_3702_, 1, v_currRecDepth_3696_);
lean_ctor_set(v___x_3702_, 2, v_ref_3701_);
lean_ctor_set_uint16(v___x_3702_, sizeof(void*)*3, v_optionFlags_3698_);
lean_ctor_set_uint8(v___x_3702_, sizeof(void*)*3 + 2, v_suppressElabErrors_3699_);
lean_ctor_set_uint8(v___x_3702_, sizeof(void*)*3 + 3, v_isRecordingDeps_3700_);
v___x_3703_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_3702_, v_a_3528_);
lean_dec_ref_known(v___x_3702_, 3);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_dec_ref_known(v___x_3703_, 1);
v___y_3583_ = v_k_3694_;
v___y_3584_ = v_a_3685_;
v___y_3585_ = v_a_3523_;
v___y_3586_ = v_a_3524_;
v___y_3587_ = v_a_3525_;
v___y_3588_ = v_a_3526_;
v___y_3589_ = v_a_3527_;
v___y_3590_ = v_a_3528_;
goto v___jp_3582_;
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v_a_3685_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3703_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3703_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
v___y_3583_ = v_k_3694_;
v___y_3584_ = v_a_3685_;
v___y_3585_ = v_a_3523_;
v___y_3586_ = v_a_3524_;
v___y_3587_ = v_a_3525_;
v___y_3588_ = v_a_3526_;
v___y_3589_ = v_a_3527_;
v___y_3590_ = v_a_3528_;
goto v___jp_3582_;
}
}
else
{
lean_object* v_toCold_3712_; lean_object* v_currRecDepth_3713_; lean_object* v_ref_3714_; uint16_t v_optionFlags_3715_; uint8_t v_suppressElabErrors_3716_; uint8_t v_isRecordingDeps_3717_; uint8_t v___x_3718_; lean_object* v_ref_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v_toCold_3712_ = lean_ctor_get(v_a_3527_, 0);
v_currRecDepth_3713_ = lean_ctor_get(v_a_3527_, 1);
v_ref_3714_ = lean_ctor_get(v_a_3527_, 2);
v_optionFlags_3715_ = lean_ctor_get_uint16(v_a_3527_, sizeof(void*)*3);
v_suppressElabErrors_3716_ = lean_ctor_get_uint8(v_a_3527_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3717_ = lean_ctor_get_uint8(v_a_3527_, sizeof(void*)*3 + 3);
v___x_3718_ = 0;
v_ref_3719_ = l_Lean_replaceRef(v_p_3517_, v_ref_3714_);
lean_dec(v_p_3517_);
lean_inc(v_currRecDepth_3713_);
lean_inc_ref(v_toCold_3712_);
v___x_3720_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3720_, 0, v_toCold_3712_);
lean_ctor_set(v___x_3720_, 1, v_currRecDepth_3713_);
lean_ctor_set(v___x_3720_, 2, v_ref_3719_);
lean_ctor_set_uint16(v___x_3720_, sizeof(void*)*3, v_optionFlags_3715_);
lean_ctor_set_uint8(v___x_3720_, sizeof(void*)*3 + 2, v_suppressElabErrors_3716_);
lean_ctor_set_uint8(v___x_3720_, sizeof(void*)*3 + 3, v_isRecordingDeps_3717_);
v___x_3721_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3516_, v_id_3519_, v_a_3685_, v_k_3694_, v_minIndexable_3520_, v___x_3718_, v___x_3686_, v_a_3525_, v_a_3526_, v___x_3720_, v_a_3528_);
lean_dec_ref_known(v___x_3720_, 3);
return v___x_3721_;
}
}
case 1:
{
lean_del_object(v___x_3692_);
lean_dec(v_id_3519_);
if (v_incremental_3522_ == 0)
{
uint8_t v_eager_3722_; 
v_eager_3722_ = lean_ctor_get_uint8(v_a_3690_, 0);
lean_dec_ref_known(v_a_3690_, 0);
v___y_3633_ = v_a_3685_;
v___y_3634_ = v_eager_3722_;
v___y_3635_ = v_a_3525_;
v___y_3636_ = v_a_3526_;
v___y_3637_ = v_a_3527_;
v___y_3638_ = v_a_3528_;
goto v___jp_3632_;
}
else
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec_ref_known(v_a_3690_, 0);
lean_dec(v_a_3685_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v___x_3723_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3724_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3723_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3724_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3724_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
case 2:
{
uint8_t v___x_3733_; lean_object* v___x_3734_; 
lean_del_object(v___x_3692_);
v___x_3733_ = 0;
lean_inc(v_a_3685_);
v___x_3734_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3685_, v___x_3733_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___x_3734_, 1);
if (lean_obj_tag(v_a_3735_) == 1)
{
lean_dec(v_a_3685_);
if (v_incremental_3522_ == 0)
{
lean_object* v_val_3736_; 
v_val_3736_ = lean_ctor_get(v_a_3735_, 0);
lean_inc(v_val_3736_);
lean_dec_ref_known(v_a_3735_, 1);
v___y_3675_ = v_val_3736_;
v___y_3676_ = v_a_3523_;
v___y_3677_ = v_a_3524_;
v___y_3678_ = v_a_3525_;
v___y_3679_ = v_a_3526_;
v___y_3680_ = v_a_3527_;
v___y_3681_ = v_a_3528_;
goto v___jp_3674_;
}
else
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec_ref_known(v_a_3735_, 1);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v___x_3737_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3738_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3737_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3738_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_dec(v_a_3735_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v___x_3747_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_3748_ = l_Lean_MessageData_ofConstName(v_a_3685_, v___x_3733_);
v___x_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_3751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3749_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3751_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3752_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3752_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_a_3685_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_a_3761_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3734_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3734_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
case 3:
{
lean_del_object(v___x_3692_);
v___y_3531_ = v___x_3686_;
v___y_3532_ = v_a_3685_;
v___y_3533_ = v_a_3523_;
v___y_3534_ = v_a_3524_;
v___y_3535_ = v_a_3525_;
v___y_3536_ = v_a_3526_;
v___y_3537_ = v_a_3527_;
v___y_3538_ = v_a_3528_;
goto v___jp_3530_;
}
case 4:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_del_object(v___x_3692_);
lean_dec(v_a_3685_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v___x_3769_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_3770_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3769_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3770_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3770_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
case 5:
{
lean_object* v_prio_3779_; lean_object* v___x_3780_; 
lean_del_object(v___x_3692_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
v_prio_3779_ = lean_ctor_get(v_a_3690_, 0);
lean_inc(v_prio_3779_);
lean_dec_ref_known(v_a_3690_, 1);
v___x_3780_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3520_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3804_; 
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3804_ == 0)
{
lean_object* v_unused_3805_; 
v_unused_3805_ = lean_ctor_get(v___x_3780_, 0);
lean_dec(v_unused_3805_);
v___x_3782_ = v___x_3780_;
v_isShared_3783_ = v_isSharedCheck_3804_;
goto v_resetjp_3781_;
}
else
{
lean_dec(v___x_3780_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3804_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v_config_3784_; lean_object* v_extensions_3785_; lean_object* v_extra_3786_; lean_object* v_extraInj_3787_; lean_object* v_extraFacts_3788_; lean_object* v_symPrios_3789_; lean_object* v_norm_3790_; lean_object* v_normProcs_3791_; lean_object* v_anchorRefs_x3f_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3803_; 
v_config_3784_ = lean_ctor_get(v_params_3516_, 0);
v_extensions_3785_ = lean_ctor_get(v_params_3516_, 1);
v_extra_3786_ = lean_ctor_get(v_params_3516_, 2);
v_extraInj_3787_ = lean_ctor_get(v_params_3516_, 3);
v_extraFacts_3788_ = lean_ctor_get(v_params_3516_, 4);
v_symPrios_3789_ = lean_ctor_get(v_params_3516_, 5);
v_norm_3790_ = lean_ctor_get(v_params_3516_, 6);
v_normProcs_3791_ = lean_ctor_get(v_params_3516_, 7);
v_anchorRefs_x3f_3792_ = lean_ctor_get(v_params_3516_, 8);
v_isSharedCheck_3803_ = !lean_is_exclusive(v_params_3516_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3794_ = v_params_3516_;
v_isShared_3795_ = v_isSharedCheck_3803_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_anchorRefs_x3f_3792_);
lean_inc(v_normProcs_3791_);
lean_inc(v_norm_3790_);
lean_inc(v_symPrios_3789_);
lean_inc(v_extraFacts_3788_);
lean_inc(v_extraInj_3787_);
lean_inc(v_extra_3786_);
lean_inc(v_extensions_3785_);
lean_inc(v_config_3784_);
lean_dec(v_params_3516_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3803_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3796_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_3789_, v_a_3685_, v_prio_3779_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 5, v___x_3796_);
v___x_3798_ = v___x_3794_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_config_3784_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_extensions_3785_);
lean_ctor_set(v_reuseFailAlloc_3802_, 2, v_extra_3786_);
lean_ctor_set(v_reuseFailAlloc_3802_, 3, v_extraInj_3787_);
lean_ctor_set(v_reuseFailAlloc_3802_, 4, v_extraFacts_3788_);
lean_ctor_set(v_reuseFailAlloc_3802_, 5, v___x_3796_);
lean_ctor_set(v_reuseFailAlloc_3802_, 6, v_norm_3790_);
lean_ctor_set(v_reuseFailAlloc_3802_, 7, v_normProcs_3791_);
lean_ctor_set(v_reuseFailAlloc_3802_, 8, v_anchorRefs_x3f_3792_);
v___x_3798_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3800_; 
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v___x_3798_);
v___x_3800_ = v___x_3782_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec(v_prio_3779_);
lean_dec(v_a_3685_);
lean_dec_ref(v_params_3516_);
v_a_3806_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3780_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3780_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
case 6:
{
lean_object* v___x_3814_; 
lean_del_object(v___x_3692_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
v___x_3814_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3685_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3839_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3817_ = v___x_3814_;
v_isShared_3818_ = v_isSharedCheck_3839_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3814_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3839_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v_config_3819_; lean_object* v_extensions_3820_; lean_object* v_extra_3821_; lean_object* v_extraInj_3822_; lean_object* v_extraFacts_3823_; lean_object* v_symPrios_3824_; lean_object* v_norm_3825_; lean_object* v_normProcs_3826_; lean_object* v_anchorRefs_x3f_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3838_; 
v_config_3819_ = lean_ctor_get(v_params_3516_, 0);
v_extensions_3820_ = lean_ctor_get(v_params_3516_, 1);
v_extra_3821_ = lean_ctor_get(v_params_3516_, 2);
v_extraInj_3822_ = lean_ctor_get(v_params_3516_, 3);
v_extraFacts_3823_ = lean_ctor_get(v_params_3516_, 4);
v_symPrios_3824_ = lean_ctor_get(v_params_3516_, 5);
v_norm_3825_ = lean_ctor_get(v_params_3516_, 6);
v_normProcs_3826_ = lean_ctor_get(v_params_3516_, 7);
v_anchorRefs_x3f_3827_ = lean_ctor_get(v_params_3516_, 8);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_params_3516_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3829_ = v_params_3516_;
v_isShared_3830_ = v_isSharedCheck_3838_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_anchorRefs_x3f_3827_);
lean_inc(v_normProcs_3826_);
lean_inc(v_norm_3825_);
lean_inc(v_symPrios_3824_);
lean_inc(v_extraFacts_3823_);
lean_inc(v_extraInj_3822_);
lean_inc(v_extra_3821_);
lean_inc(v_extensions_3820_);
lean_inc(v_config_3819_);
lean_dec(v_params_3516_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3838_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3831_ = l_Lean_PersistentArray_push___redArg(v_extraInj_3822_, v_a_3815_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 3, v___x_3831_);
v___x_3833_ = v___x_3829_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_config_3819_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v_extensions_3820_);
lean_ctor_set(v_reuseFailAlloc_3837_, 2, v_extra_3821_);
lean_ctor_set(v_reuseFailAlloc_3837_, 3, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3837_, 4, v_extraFacts_3823_);
lean_ctor_set(v_reuseFailAlloc_3837_, 5, v_symPrios_3824_);
lean_ctor_set(v_reuseFailAlloc_3837_, 6, v_norm_3825_);
lean_ctor_set(v_reuseFailAlloc_3837_, 7, v_normProcs_3826_);
lean_ctor_set(v_reuseFailAlloc_3837_, 8, v_anchorRefs_x3f_3827_);
v___x_3833_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3835_; 
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v___x_3833_);
v___x_3835_ = v___x_3817_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3833_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_dec_ref(v_params_3516_);
v_a_3840_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3814_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3814_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
case 7:
{
lean_object* v___x_3848_; lean_object* v___x_3850_; 
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
v___x_3848_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3516_, v_a_3685_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v___x_3848_);
v___x_3850_ = v___x_3692_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
case 8:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec_ref_known(v_a_3690_, 0);
lean_del_object(v___x_3692_);
lean_dec(v_a_3685_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v___x_3852_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_3853_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3852_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3853_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3853_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
case 9:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_del_object(v___x_3692_);
lean_dec(v_a_3685_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v___x_3862_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_3863_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3862_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3863_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3863_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
case 10:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref_known(v_a_3690_, 0);
lean_del_object(v___x_3692_);
lean_dec(v_a_3685_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v___x_3872_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_3873_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3872_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3873_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3873_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
default: 
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_del_object(v___x_3692_);
lean_dec(v_a_3685_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v___x_3882_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
v___x_3883_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3882_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3883_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3883_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_dec(v_a_3685_);
lean_dec(v_id_3519_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_a_3893_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3689_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3689_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3518_);
v___y_3531_ = v___x_3686_;
v___y_3532_ = v_a_3685_;
v___y_3533_ = v_a_3523_;
v___y_3534_ = v_a_3524_;
v___y_3535_ = v_a_3525_;
v___y_3536_ = v_a_3526_;
v___y_3537_ = v_a_3527_;
v___y_3538_ = v_a_3528_;
goto v___jp_3530_;
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_dec(v_a_3685_);
lean_dec(v_id_3519_);
lean_dec(v_mod_x3f_3518_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_a_3901_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3687_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3687_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
v___jp_3909_:
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3920_; 
v_a_3911_ = lean_ctor_get(v___y_3910_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___y_3910_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3913_ = v___y_3910_;
v_isShared_3914_ = v_isSharedCheck_3920_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___y_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3920_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
if (lean_obj_tag(v_a_3911_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3917_; 
lean_dec(v_id_3519_);
lean_dec(v_mod_x3f_3518_);
lean_dec(v_p_3517_);
lean_dec_ref(v_params_3516_);
v_a_3915_ = lean_ctor_get(v_a_3911_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v_a_3911_, 1);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v_a_3915_);
v___x_3917_ = v___x_3913_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3915_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
else
{
lean_object* v_a_3919_; 
lean_del_object(v___x_3913_);
v_a_3919_ = lean_ctor_get(v_a_3911_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v_a_3911_, 1);
v_a_3685_ = v_a_3919_;
goto v___jp_3684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4000_, lean_object* v_p_4001_, lean_object* v_mod_x3f_4002_, lean_object* v_id_4003_, lean_object* v_minIndexable_4004_, lean_object* v_only_4005_, lean_object* v_incremental_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
uint8_t v_minIndexable_boxed_4014_; uint8_t v_only_boxed_4015_; uint8_t v_incremental_boxed_4016_; lean_object* v_res_4017_; 
v_minIndexable_boxed_4014_ = lean_unbox(v_minIndexable_4004_);
v_only_boxed_4015_ = lean_unbox(v_only_4005_);
v_incremental_boxed_4016_ = lean_unbox(v_incremental_4006_);
v_res_4017_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4000_, v_p_4001_, v_mod_x3f_4002_, v_id_4003_, v_minIndexable_boxed_4014_, v_only_boxed_4015_, v_incremental_boxed_4016_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4018_, lean_object* v_id_4019_, uint8_t v_minIndexable_4020_, lean_object* v_as_4021_, lean_object* v_as_x27_4022_, lean_object* v_b_4023_, lean_object* v_a_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4018_, v_id_4019_, v_minIndexable_4020_, v_as_x27_4022_, v_b_4023_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4033_, lean_object* v_id_4034_, lean_object* v_minIndexable_4035_, lean_object* v_as_4036_, lean_object* v_as_x27_4037_, lean_object* v_b_4038_, lean_object* v_a_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
uint8_t v_minIndexable_boxed_4047_; lean_object* v_res_4048_; 
v_minIndexable_boxed_4047_ = lean_unbox(v_minIndexable_4035_);
v_res_4048_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4033_, v_id_4034_, v_minIndexable_boxed_4047_, v_as_4036_, v_as_x27_4037_, v_b_4038_, v_a_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v_as_x27_4037_);
lean_dec(v_as_4036_);
lean_dec(v_p_4033_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4049_, lean_object* v_as_x27_4050_, lean_object* v_b_4051_, lean_object* v_a_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4050_, v_b_4051_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4061_, lean_object* v_as_x27_4062_, lean_object* v_b_4063_, lean_object* v_a_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4061_, v_as_x27_4062_, v_b_4063_, v_a_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v_as_x27_4062_);
lean_dec(v_as_4061_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4073_, lean_object* v_ref_4074_, lean_object* v_msg_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4074_, v_msg_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4084_, lean_object* v_ref_4085_, lean_object* v_msg_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4084_, v_ref_4085_, v_msg_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v_ref_4085_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4095_, lean_object* v_id_4096_, uint8_t v_minIndexable_4097_, lean_object* v_as_4098_, lean_object* v_as_x27_4099_, lean_object* v_b_4100_, lean_object* v_a_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4095_, v_id_4096_, v_minIndexable_4097_, v_as_x27_4099_, v_b_4100_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4110_, lean_object* v_id_4111_, lean_object* v_minIndexable_4112_, lean_object* v_as_4113_, lean_object* v_as_x27_4114_, lean_object* v_b_4115_, lean_object* v_a_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
uint8_t v_minIndexable_boxed_4124_; lean_object* v_res_4125_; 
v_minIndexable_boxed_4124_ = lean_unbox(v_minIndexable_4112_);
v_res_4125_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4110_, v_id_4111_, v_minIndexable_boxed_4124_, v_as_4113_, v_as_x27_4114_, v_b_4115_, v_a_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v_as_x27_4114_);
lean_dec(v_as_4113_);
lean_dec(v_p_4110_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4126_, lean_object* v_t_4127_, lean_object* v_k_4128_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4127_, v_k_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4130_, lean_object* v_t_4131_, lean_object* v_k_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4130_, v_t_4131_, v_k_4132_);
lean_dec(v_k_4132_);
lean_dec(v_t_4131_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4134_, uint8_t v_skipAuxDecl_4135_, lean_object* v_auxDeclToFullName_4136_, lean_object* v___x_4137_, lean_object* v_givenNameView_4138_, lean_object* v_as_4139_, lean_object* v_i_4140_, lean_object* v_a_4141_){
_start:
{
lean_object* v___x_4142_; 
v___x_4142_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4134_, v_skipAuxDecl_4135_, v_auxDeclToFullName_4136_, v___x_4137_, v_givenNameView_4138_, v_as_4139_, v_i_4140_);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4143_, lean_object* v_skipAuxDecl_4144_, lean_object* v_auxDeclToFullName_4145_, lean_object* v___x_4146_, lean_object* v_givenNameView_4147_, lean_object* v_as_4148_, lean_object* v_i_4149_, lean_object* v_a_4150_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4151_; lean_object* v_res_4152_; 
v_skipAuxDecl_boxed_4151_ = lean_unbox(v_skipAuxDecl_4144_);
v_res_4152_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4143_, v_skipAuxDecl_boxed_4151_, v_auxDeclToFullName_4145_, v___x_4146_, v_givenNameView_4147_, v_as_4148_, v_i_4149_, v_a_4150_);
lean_dec_ref(v_as_4148_);
lean_dec(v_auxDeclToFullName_4145_);
lean_dec(v_givenName_4143_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4153_, lean_object* v_givenName_4154_, lean_object* v_as_4155_, lean_object* v_i_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4153_, v_givenName_4154_, v_as_4155_, v_i_4156_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4159_, lean_object* v_givenName_4160_, lean_object* v_as_4161_, lean_object* v_i_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4159_, v_givenName_4160_, v_as_4161_, v_i_4162_, v_a_4163_);
lean_dec_ref(v_as_4161_);
lean_dec(v_givenName_4160_);
lean_dec(v_localDecl_x3f_4159_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4165_, uint8_t v_skipAuxDecl_4166_, lean_object* v_auxDeclToFullName_4167_, lean_object* v___x_4168_, lean_object* v_givenNameView_4169_, lean_object* v_as_4170_, lean_object* v_i_4171_, lean_object* v_a_4172_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4165_, v_skipAuxDecl_4166_, v_auxDeclToFullName_4167_, v___x_4168_, v_givenNameView_4169_, v_as_4170_, v_i_4171_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4174_, lean_object* v_skipAuxDecl_4175_, lean_object* v_auxDeclToFullName_4176_, lean_object* v___x_4177_, lean_object* v_givenNameView_4178_, lean_object* v_as_4179_, lean_object* v_i_4180_, lean_object* v_a_4181_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4182_; lean_object* v_res_4183_; 
v_skipAuxDecl_boxed_4182_ = lean_unbox(v_skipAuxDecl_4175_);
v_res_4183_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4174_, v_skipAuxDecl_boxed_4182_, v_auxDeclToFullName_4176_, v___x_4177_, v_givenNameView_4178_, v_as_4179_, v_i_4180_, v_a_4181_);
lean_dec_ref(v_as_4179_);
lean_dec(v_auxDeclToFullName_4176_);
lean_dec(v_givenName_4174_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4184_, lean_object* v_givenName_4185_, lean_object* v_as_4186_, lean_object* v_i_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v___x_4189_; 
v___x_4189_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4184_, v_givenName_4185_, v_as_4186_, v_i_4187_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4190_, lean_object* v_givenName_4191_, lean_object* v_as_4192_, lean_object* v_i_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4190_, v_givenName_4191_, v_as_4192_, v_i_4193_, v_a_4194_);
lean_dec_ref(v_as_4192_);
lean_dec(v_givenName_4191_);
lean_dec(v_localDecl_x3f_4190_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4196_, v___y_4201_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec_ref(v_opt_4205_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4214_, lean_object* v_msgData_4215_, uint8_t v_severity_4216_, uint8_t v_isSilent_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4214_, v_msgData_4215_, v_severity_4216_, v_isSilent_4217_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4226_, lean_object* v_msgData_4227_, lean_object* v_severity_4228_, lean_object* v_isSilent_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
uint8_t v_severity_boxed_4237_; uint8_t v_isSilent_boxed_4238_; lean_object* v_res_4239_; 
v_severity_boxed_4237_ = lean_unbox(v_severity_4228_);
v_isSilent_boxed_4238_ = lean_unbox(v_isSilent_4229_);
v_res_4239_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4226_, v_msgData_4227_, v_severity_boxed_4237_, v_isSilent_boxed_4238_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v_ref_4226_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4240_, uint8_t v___x_4241_, lean_object* v_b_4242_, lean_object* v_____r_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4251_ = lean_box(0);
v___x_4252_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4240_, v___x_4251_, v___y_4248_, v___y_4249_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4254_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc_n(v_a_4253_, 2);
lean_dec_ref_known(v___x_4252_, 1);
v___x_4254_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4253_, v___x_4241_, v___y_4244_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
if (lean_obj_tag(v___x_4254_) == 0)
{
uint8_t v___x_4255_; lean_object* v___x_4256_; 
lean_dec_ref_known(v___x_4254_, 1);
v___x_4255_ = 0;
lean_inc(v_a_4253_);
v___x_4256_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4253_, v___x_4255_, v___y_4248_, v___y_4249_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4316_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4259_ = v___x_4256_;
v_isShared_4260_ = v_isSharedCheck_4316_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4256_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4316_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
if (lean_obj_tag(v_a_4257_) == 1)
{
lean_object* v_val_4261_; lean_object* v___x_4262_; 
lean_del_object(v___x_4259_);
lean_dec(v_a_4253_);
v_val_4261_ = lean_ctor_get(v_a_4257_, 0);
lean_inc_n(v_val_4261_, 2);
lean_dec_ref_known(v_a_4257_, 1);
v___x_4262_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4261_, v___y_4248_, v___y_4249_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v___x_4263_; 
lean_dec_ref_known(v___x_4262_, 1);
v___x_4263_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4242_, v_val_4261_, v___y_4248_, v___y_4249_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4273_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4266_ = v___x_4263_;
v_isShared_4267_ = v_isSharedCheck_4273_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4263_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4273_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4271_; 
v___x_4268_ = lean_box(0);
v___x_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
lean_ctor_set(v___x_4269_, 1, v_a_4264_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 0, v___x_4269_);
v___x_4271_ = v___x_4266_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4269_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
else
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
v_a_4274_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4263_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4263_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
lean_dec(v_val_4261_);
lean_dec_ref(v_b_4242_);
v_a_4282_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4262_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4262_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
}
else
{
uint8_t v___x_4290_; 
lean_dec(v_a_4257_);
lean_inc(v_a_4253_);
v___x_4290_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4242_, v_a_4253_);
if (v___x_4290_ == 0)
{
lean_object* v___x_4291_; 
lean_del_object(v___x_4259_);
v___x_4291_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4242_, v_a_4253_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4301_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4294_ = v___x_4291_;
v_isShared_4295_ = v_isSharedCheck_4301_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4291_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4301_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4299_; 
v___x_4296_ = lean_box(0);
v___x_4297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4296_);
lean_ctor_set(v___x_4297_, 1, v_a_4292_);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 0, v___x_4297_);
v___x_4299_ = v___x_4294_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4297_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
v_a_4302_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4291_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4291_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
else
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4314_; 
v___x_4310_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4242_, v_a_4253_);
v___x_4311_ = lean_box(0);
v___x_4312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4311_);
lean_ctor_set(v___x_4312_, 1, v___x_4310_);
if (v_isShared_4260_ == 0)
{
lean_ctor_set(v___x_4259_, 0, v___x_4312_);
v___x_4314_ = v___x_4259_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4312_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4324_; 
lean_dec(v_a_4253_);
lean_dec_ref(v_b_4242_);
v_a_4317_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4319_ = v___x_4256_;
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4256_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4322_; 
if (v_isShared_4320_ == 0)
{
v___x_4322_ = v___x_4319_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_a_4317_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec(v_a_4253_);
lean_dec_ref(v_b_4242_);
v_a_4325_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4254_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4254_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_dec_ref(v_b_4242_);
v_a_4333_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4252_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4252_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4341_, lean_object* v___x_4342_, lean_object* v_b_4343_, lean_object* v_____r_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
uint8_t v___x_17514__boxed_4352_; lean_object* v_res_4353_; 
v___x_17514__boxed_4352_ = lean_unbox(v___x_4342_);
v_res_4353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4341_, v___x_17514__boxed_4352_, v_b_4343_, v_____r_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4357_, lean_object* v_b_4358_, lean_object* v_a_4359_, uint8_t v___x_4360_, uint8_t v_only_4361_, uint8_t v_incremental_4362_, lean_object* v_x_4363_, lean_object* v_mod_x3f_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4372_ = lean_unsigned_to_nat(1u);
v___x_4373_ = l_Lean_Syntax_getArg(v___x_4357_, v___x_4372_);
if (v___x_4360_ == 0)
{
lean_object* v___x_4434_; uint8_t v___x_4435_; 
v___x_4434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4373_);
v___x_4435_ = l_Lean_Syntax_isOfKind(v___x_4373_, v___x_4434_);
if (v___x_4435_ == 0)
{
lean_object* v___x_4436_; 
v___x_4436_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4358_, v_a_4359_, v_mod_x3f_4364_, v___x_4373_, v___x_4360_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4446_; 
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4439_ = v___x_4436_;
v_isShared_4440_ = v_isSharedCheck_4446_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4436_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4446_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4444_; 
v___x_4441_ = lean_box(0);
v___x_4442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
lean_ctor_set(v___x_4442_, 1, v_a_4437_);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 0, v___x_4442_);
v___x_4444_ = v___x_4439_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v___x_4442_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
v_a_4447_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4436_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4436_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
else
{
goto v___jp_4394_;
}
}
else
{
goto v___jp_4394_;
}
v___jp_4374_:
{
lean_object* v___x_4375_; 
v___x_4375_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4358_, v_a_4359_, v_mod_x3f_4364_, v___x_4373_, v___x_4360_, v_only_4361_, v_incremental_4362_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4385_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4385_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4385_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4383_; 
v___x_4380_ = lean_box(0);
v___x_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4380_);
lean_ctor_set(v___x_4381_, 1, v_a_4376_);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4381_);
v___x_4383_ = v___x_4378_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4381_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
v_a_4386_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4375_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4375_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
v___jp_4394_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4395_ = l_Lean_TSyntax_getId(v___x_4373_);
v___x_4396_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4395_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_a_4397_);
lean_dec_ref_known(v___x_4396_, 1);
if (lean_obj_tag(v_a_4397_) == 1)
{
lean_object* v_val_4398_; lean_object* v_snd_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4424_; 
v_val_4398_ = lean_ctor_get(v_a_4397_, 0);
lean_inc(v_val_4398_);
lean_dec_ref_known(v_a_4397_, 1);
v_snd_4399_ = lean_ctor_get(v_val_4398_, 1);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_val_4398_);
if (v_isSharedCheck_4424_ == 0)
{
lean_object* v_unused_4425_; 
v_unused_4425_ = lean_ctor_get(v_val_4398_, 0);
lean_dec(v_unused_4425_);
v___x_4401_ = v_val_4398_;
v_isShared_4402_ = v_isSharedCheck_4424_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_snd_4399_);
lean_dec(v_val_4398_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4424_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
if (lean_obj_tag(v_snd_4399_) == 1)
{
lean_object* v___x_4403_; 
lean_dec_ref_known(v_snd_4399_, 2);
v___x_4403_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4358_, v_a_4359_, v_mod_x3f_4364_, v___x_4373_, v___x_4360_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4415_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4406_ = v___x_4403_;
v_isShared_4407_ = v_isSharedCheck_4415_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4403_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4415_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4408_; lean_object* v___x_4410_; 
v___x_4408_ = lean_box(0);
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 1, v_a_4404_);
lean_ctor_set(v___x_4401_, 0, v___x_4408_);
v___x_4410_ = v___x_4401_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4408_);
lean_ctor_set(v_reuseFailAlloc_4414_, 1, v_a_4404_);
v___x_4410_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
lean_object* v___x_4412_; 
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 0, v___x_4410_);
v___x_4412_ = v___x_4406_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4410_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_del_object(v___x_4401_);
v_a_4416_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4403_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4403_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
else
{
lean_del_object(v___x_4401_);
lean_dec(v_snd_4399_);
goto v___jp_4374_;
}
}
}
else
{
lean_dec(v_a_4397_);
goto v___jp_4374_;
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_dec(v___x_4373_);
lean_dec(v_mod_x3f_4364_);
lean_dec(v_a_4359_);
lean_dec_ref(v_b_4358_);
v_a_4426_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4396_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4396_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4455_, lean_object* v_b_4456_, lean_object* v_a_4457_, lean_object* v___x_4458_, lean_object* v_only_4459_, lean_object* v_incremental_4460_, lean_object* v_x_4461_, lean_object* v_mod_x3f_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_){
_start:
{
uint8_t v___x_17732__boxed_4470_; uint8_t v_only_boxed_4471_; uint8_t v_incremental_boxed_4472_; lean_object* v_res_4473_; 
v___x_17732__boxed_4470_ = lean_unbox(v___x_4458_);
v_only_boxed_4471_ = lean_unbox(v_only_4459_);
v_incremental_boxed_4472_ = lean_unbox(v_incremental_4460_);
v_res_4473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4455_, v_b_4456_, v_a_4457_, v___x_17732__boxed_4470_, v_only_boxed_4471_, v_incremental_boxed_4472_, v_x_4461_, v_mod_x3f_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v___x_4455_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4474_, lean_object* v___x_4475_, lean_object* v_____r_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v___x_4484_; 
v___x_4484_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4474_, v___x_4475_, v___y_4481_, v___y_4482_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4494_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4487_ = v___x_4484_;
v_isShared_4488_ = v_isSharedCheck_4494_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4494_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4492_; 
v___x_4489_ = lean_box(0);
v___x_4490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4489_);
lean_ctor_set(v___x_4490_, 1, v_a_4485_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 0, v___x_4490_);
v___x_4492_ = v___x_4487_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4490_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
v_a_4495_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4484_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4484_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4503_, lean_object* v___x_4504_, lean_object* v_____r_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4503_, v___x_4504_, v_____r_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___x_4504_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4514_, lean_object* v_b_4515_, lean_object* v_a_4516_, uint8_t v___x_4517_, uint8_t v_only_4518_, uint8_t v_incremental_4519_, uint8_t v___x_4520_, lean_object* v_x_4521_, lean_object* v_mod_x3f_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4530_ = lean_unsigned_to_nat(2u);
v___x_4531_ = l_Lean_Syntax_getArg(v___x_4514_, v___x_4530_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4592_; uint8_t v___x_4593_; 
v___x_4592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4531_);
v___x_4593_ = l_Lean_Syntax_isOfKind(v___x_4531_, v___x_4592_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; 
v___x_4594_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4515_, v_a_4516_, v_mod_x3f_4522_, v___x_4531_, v___x_4517_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4604_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4597_ = v___x_4594_;
v_isShared_4598_ = v_isSharedCheck_4604_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4594_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4604_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4602_; 
v___x_4599_ = lean_box(0);
v___x_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4599_);
lean_ctor_set(v___x_4600_, 1, v_a_4595_);
if (v_isShared_4598_ == 0)
{
lean_ctor_set(v___x_4597_, 0, v___x_4600_);
v___x_4602_ = v___x_4597_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4600_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
else
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
v_a_4605_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4594_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4594_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
}
else
{
goto v___jp_4552_;
}
}
else
{
goto v___jp_4552_;
}
v___jp_4532_:
{
lean_object* v___x_4533_; 
v___x_4533_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4515_, v_a_4516_, v_mod_x3f_4522_, v___x_4531_, v___x_4517_, v_only_4518_, v_incremental_4519_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4543_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4543_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4543_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4541_; 
v___x_4538_ = lean_box(0);
v___x_4539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4538_);
lean_ctor_set(v___x_4539_, 1, v_a_4534_);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v___x_4539_);
v___x_4541_ = v___x_4536_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4539_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
v_a_4544_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4533_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4533_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
v___jp_4552_:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4553_ = l_Lean_TSyntax_getId(v___x_4531_);
v___x_4554_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4553_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_object* v_a_4555_; 
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_a_4555_);
lean_dec_ref_known(v___x_4554_, 1);
if (lean_obj_tag(v_a_4555_) == 1)
{
lean_object* v_val_4556_; lean_object* v_snd_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4582_; 
v_val_4556_ = lean_ctor_get(v_a_4555_, 0);
lean_inc(v_val_4556_);
lean_dec_ref_known(v_a_4555_, 1);
v_snd_4557_ = lean_ctor_get(v_val_4556_, 1);
v_isSharedCheck_4582_ = !lean_is_exclusive(v_val_4556_);
if (v_isSharedCheck_4582_ == 0)
{
lean_object* v_unused_4583_; 
v_unused_4583_ = lean_ctor_get(v_val_4556_, 0);
lean_dec(v_unused_4583_);
v___x_4559_ = v_val_4556_;
v_isShared_4560_ = v_isSharedCheck_4582_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_snd_4557_);
lean_dec(v_val_4556_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4582_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
if (lean_obj_tag(v_snd_4557_) == 1)
{
lean_object* v___x_4561_; 
lean_dec_ref_known(v_snd_4557_, 2);
v___x_4561_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4515_, v_a_4516_, v_mod_x3f_4522_, v___x_4531_, v___x_4517_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4573_; 
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4564_ = v___x_4561_;
v_isShared_4565_ = v_isSharedCheck_4573_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4561_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4573_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4566_; lean_object* v___x_4568_; 
v___x_4566_ = lean_box(0);
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 1, v_a_4562_);
lean_ctor_set(v___x_4559_, 0, v___x_4566_);
v___x_4568_ = v___x_4559_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4566_);
lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_a_4562_);
v___x_4568_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
lean_object* v___x_4570_; 
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v___x_4568_);
v___x_4570_ = v___x_4564_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4568_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
}
else
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4581_; 
lean_del_object(v___x_4559_);
v_a_4574_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4576_ = v___x_4561_;
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4561_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4579_; 
if (v_isShared_4577_ == 0)
{
v___x_4579_ = v___x_4576_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4574_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
}
else
{
lean_del_object(v___x_4559_);
lean_dec(v_snd_4557_);
goto v___jp_4532_;
}
}
}
else
{
lean_dec(v_a_4555_);
goto v___jp_4532_;
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_dec(v___x_4531_);
lean_dec(v_mod_x3f_4522_);
lean_dec(v_a_4516_);
lean_dec_ref(v_b_4515_);
v_a_4584_ = lean_ctor_get(v___x_4554_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4554_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4554_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4613_, lean_object* v_b_4614_, lean_object* v_a_4615_, lean_object* v___x_4616_, lean_object* v_only_4617_, lean_object* v_incremental_4618_, lean_object* v___x_4619_, lean_object* v_x_4620_, lean_object* v_mod_x3f_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
uint8_t v___x_18001__boxed_4629_; uint8_t v_only_boxed_4630_; uint8_t v_incremental_boxed_4631_; uint8_t v___x_18002__boxed_4632_; lean_object* v_res_4633_; 
v___x_18001__boxed_4629_ = lean_unbox(v___x_4616_);
v_only_boxed_4630_ = lean_unbox(v_only_4617_);
v_incremental_boxed_4631_ = lean_unbox(v_incremental_4618_);
v___x_18002__boxed_4632_ = lean_unbox(v___x_4619_);
v_res_4633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4613_, v_b_4614_, v_a_4615_, v___x_18001__boxed_4629_, v_only_boxed_4630_, v_incremental_boxed_4631_, v___x_18002__boxed_4632_, v_x_4620_, v_mod_x3f_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___x_4613_);
return v_res_4633_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4642_ = l_Lean_stringToMessageData(v___x_4641_);
return v___x_4642_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13(void){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12));
v___x_4669_ = l_Lean_stringToMessageData(v___x_4668_);
return v___x_4669_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4675_ = l_Lean_stringToMessageData(v___x_4674_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4676_, uint8_t v_only_4677_, uint8_t v_incremental_4678_, lean_object* v_as_4679_, size_t v_sz_4680_, size_t v_i_4681_, lean_object* v_b_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v_snd_4691_; lean_object* v___y_4696_; uint8_t v___y_4697_; lean_object* v_a_4701_; lean_object* v___y_4705_; uint8_t v___x_4709_; 
v___x_4709_ = lean_usize_dec_lt(v_i_4681_, v_sz_4680_);
if (v___x_4709_ == 0)
{
lean_object* v___x_4710_; 
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v_b_4682_);
return v___x_4710_;
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v_a_4711_ = lean_array_uget_borrowed(v_as_4679_, v_i_4681_);
v___x_4712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_4711_);
v___x_4713_ = l_Lean_Syntax_isOfKind(v_a_4711_, v___x_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4714_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4711_);
v___x_4715_ = l_Lean_MessageData_ofSyntax(v_a_4711_);
v___x_4716_ = l_Lean_indentD(v___x_4715_);
v___x_4717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4714_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4717_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_dec_ref_known(v___x_4718_, 1);
v_snd_4691_ = v_b_4682_;
goto v___jp_4690_;
}
else
{
lean_object* v_a_4719_; 
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
lean_inc(v_a_4719_);
lean_dec_ref_known(v___x_4718_, 1);
v_a_4701_ = v_a_4719_;
goto v___jp_4700_;
}
}
else
{
lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; uint8_t v___x_4723_; 
v___x_4720_ = lean_unsigned_to_nat(0u);
v___x_4721_ = l_Lean_Syntax_getArg(v_a_4711_, v___x_4720_);
v___x_4722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_4721_);
v___x_4723_ = l_Lean_Syntax_isOfKind(v___x_4721_, v___x_4722_);
if (v___x_4723_ == 0)
{
lean_object* v___x_4724_; uint8_t v___x_4725_; 
v___x_4724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_4721_);
v___x_4725_ = l_Lean_Syntax_isOfKind(v___x_4721_, v___x_4724_);
if (v___x_4725_ == 0)
{
lean_object* v___x_4726_; uint8_t v___x_4727_; 
v___x_4726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_4721_);
v___x_4727_ = l_Lean_Syntax_isOfKind(v___x_4721_, v___x_4726_);
if (v___x_4727_ == 0)
{
lean_object* v___x_4728_; uint8_t v___x_4729_; 
v___x_4728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_4721_);
v___x_4729_ = l_Lean_Syntax_isOfKind(v___x_4721_, v___x_4728_);
if (v___x_4729_ == 0)
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; 
lean_dec(v___x_4721_);
v___x_4730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4711_);
v___x_4731_ = l_Lean_MessageData_ofSyntax(v_a_4711_);
v___x_4732_ = l_Lean_indentD(v___x_4731_);
v___x_4733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4730_);
lean_ctor_set(v___x_4733_, 1, v___x_4732_);
v___x_4734_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4733_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4734_) == 0)
{
lean_dec_ref_known(v___x_4734_, 1);
v_snd_4691_ = v_b_4682_;
goto v___jp_4690_;
}
else
{
lean_object* v_a_4735_; 
v_a_4735_ = lean_ctor_get(v___x_4734_, 0);
lean_inc(v_a_4735_);
lean_dec_ref_known(v___x_4734_, 1);
v_a_4701_ = v_a_4735_;
goto v___jp_4700_;
}
}
else
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = lean_unsigned_to_nat(1u);
v___x_4737_ = l_Lean_Syntax_getArg(v___x_4721_, v___x_4736_);
lean_dec(v___x_4721_);
if (v___x_4727_ == 0)
{
lean_object* v___x_4746_; uint8_t v___x_4747_; 
v___x_4746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15));
lean_inc(v___x_4737_);
v___x_4747_ = l_Lean_Syntax_isOfKind(v___x_4737_, v___x_4746_);
if (v___x_4747_ == 0)
{
lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
lean_dec(v___x_4737_);
v___x_4748_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4711_);
v___x_4749_ = l_Lean_MessageData_ofSyntax(v_a_4711_);
v___x_4750_ = l_Lean_indentD(v___x_4749_);
v___x_4751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4748_);
lean_ctor_set(v___x_4751_, 1, v___x_4750_);
v___x_4752_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4751_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_dec_ref_known(v___x_4752_, 1);
v_snd_4691_ = v_b_4682_;
goto v___jp_4690_;
}
else
{
lean_object* v_a_4753_; 
v_a_4753_ = lean_ctor_get(v___x_4752_, 0);
lean_inc(v_a_4753_);
lean_dec_ref_known(v___x_4752_, 1);
v_a_4701_ = v_a_4753_;
goto v___jp_4700_;
}
}
else
{
goto v___jp_4738_;
}
}
else
{
goto v___jp_4738_;
}
v___jp_4738_:
{
if (v_only_4677_ == 0)
{
lean_object* v___x_4739_; lean_object* v___x_4740_; 
v___x_4739_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13);
v___x_4740_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_4737_, v___x_4739_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v_a_4741_; lean_object* v___x_4742_; 
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4741_);
lean_dec_ref_known(v___x_4740_, 1);
lean_inc_ref(v_b_4682_);
v___x_4742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4682_, v___x_4737_, v_a_4741_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___x_4737_);
v___y_4705_ = v___x_4742_;
goto v___jp_4704_;
}
else
{
lean_object* v_a_4743_; 
lean_dec(v___x_4737_);
v_a_4743_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4743_);
lean_dec_ref_known(v___x_4740_, 1);
v_a_4701_ = v_a_4743_;
goto v___jp_4700_;
}
}
else
{
lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4744_ = lean_box(0);
lean_inc_ref(v_b_4682_);
v___x_4745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4682_, v___x_4737_, v___x_4744_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___x_4737_);
v___y_4705_ = v___x_4745_;
goto v___jp_4704_;
}
}
}
}
else
{
lean_object* v___x_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; 
v___x_4754_ = lean_unsigned_to_nat(1u);
v___x_4755_ = l_Lean_Syntax_getArg(v___x_4721_, v___x_4754_);
v___x_4756_ = l_Lean_Syntax_isNone(v___x_4755_);
if (v___x_4756_ == 0)
{
uint8_t v___x_4757_; 
lean_inc(v___x_4755_);
v___x_4757_ = l_Lean_Syntax_matchesNull(v___x_4755_, v___x_4754_);
if (v___x_4757_ == 0)
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
lean_dec(v___x_4755_);
lean_dec(v___x_4721_);
v___x_4758_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4711_);
v___x_4759_ = l_Lean_MessageData_ofSyntax(v_a_4711_);
v___x_4760_ = l_Lean_indentD(v___x_4759_);
v___x_4761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4761_, 0, v___x_4758_);
lean_ctor_set(v___x_4761_, 1, v___x_4760_);
v___x_4762_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4761_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4762_) == 0)
{
lean_dec_ref_known(v___x_4762_, 1);
v_snd_4691_ = v_b_4682_;
goto v___jp_4690_;
}
else
{
lean_object* v_a_4763_; 
v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
lean_inc(v_a_4763_);
lean_dec_ref_known(v___x_4762_, 1);
v_a_4701_ = v_a_4763_;
goto v___jp_4700_;
}
}
else
{
lean_object* v___x_4764_; 
v___x_4764_ = l_Lean_Syntax_getArg(v___x_4755_, v___x_4720_);
lean_dec(v___x_4755_);
if (v___x_4756_ == 0)
{
lean_object* v___x_4769_; uint8_t v___x_4770_; 
v___x_4769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4764_);
v___x_4770_ = l_Lean_Syntax_isOfKind(v___x_4764_, v___x_4769_);
if (v___x_4770_ == 0)
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
lean_dec(v___x_4764_);
lean_dec(v___x_4721_);
v___x_4771_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4711_);
v___x_4772_ = l_Lean_MessageData_ofSyntax(v_a_4711_);
v___x_4773_ = l_Lean_indentD(v___x_4772_);
v___x_4774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4771_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
v___x_4775_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4774_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_dec_ref_known(v___x_4775_, 1);
v_snd_4691_ = v_b_4682_;
goto v___jp_4690_;
}
else
{
lean_object* v_a_4776_; 
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_a_4776_);
lean_dec_ref_known(v___x_4775_, 1);
v_a_4701_ = v_a_4776_;
goto v___jp_4700_;
}
}
else
{
goto v___jp_4765_;
}
}
else
{
goto v___jp_4765_;
}
v___jp_4765_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4766_ = lean_box(0);
v___x_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4764_);
lean_inc(v_a_4711_);
lean_inc_ref(v_b_4682_);
v___x_4768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4721_, v_b_4682_, v_a_4711_, v___x_4713_, v_only_4677_, v_incremental_4678_, v___x_4725_, v___x_4766_, v___x_4767_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___x_4721_);
v___y_4705_ = v___x_4768_;
goto v___jp_4704_;
}
}
}
else
{
lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
lean_dec(v___x_4755_);
v___x_4777_ = lean_box(0);
v___x_4778_ = lean_box(0);
lean_inc(v_a_4711_);
lean_inc_ref(v_b_4682_);
v___x_4779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4721_, v_b_4682_, v_a_4711_, v___x_4713_, v_only_4677_, v_incremental_4678_, v___x_4725_, v___x_4777_, v___x_4778_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___x_4721_);
v___y_4705_ = v___x_4779_;
goto v___jp_4704_;
}
}
}
else
{
lean_object* v___x_4780_; uint8_t v___x_4781_; 
v___x_4780_ = l_Lean_Syntax_getArg(v___x_4721_, v___x_4720_);
v___x_4781_ = l_Lean_Syntax_isNone(v___x_4780_);
if (v___x_4781_ == 0)
{
lean_object* v___x_4782_; uint8_t v___x_4783_; 
v___x_4782_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4780_);
v___x_4783_ = l_Lean_Syntax_matchesNull(v___x_4780_, v___x_4782_);
if (v___x_4783_ == 0)
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
lean_dec(v___x_4780_);
lean_dec(v___x_4721_);
v___x_4784_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4711_);
v___x_4785_ = l_Lean_MessageData_ofSyntax(v_a_4711_);
v___x_4786_ = l_Lean_indentD(v___x_4785_);
v___x_4787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4784_);
lean_ctor_set(v___x_4787_, 1, v___x_4786_);
v___x_4788_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4787_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_dec_ref_known(v___x_4788_, 1);
v_snd_4691_ = v_b_4682_;
goto v___jp_4690_;
}
else
{
lean_object* v_a_4789_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
lean_inc(v_a_4789_);
lean_dec_ref_known(v___x_4788_, 1);
v_a_4701_ = v_a_4789_;
goto v___jp_4700_;
}
}
else
{
lean_object* v___x_4790_; 
v___x_4790_ = l_Lean_Syntax_getArg(v___x_4780_, v___x_4720_);
lean_dec(v___x_4780_);
if (v___x_4781_ == 0)
{
lean_object* v___x_4795_; uint8_t v___x_4796_; 
v___x_4795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4790_);
v___x_4796_ = l_Lean_Syntax_isOfKind(v___x_4790_, v___x_4795_);
if (v___x_4796_ == 0)
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
lean_dec(v___x_4790_);
lean_dec(v___x_4721_);
v___x_4797_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4711_);
v___x_4798_ = l_Lean_MessageData_ofSyntax(v_a_4711_);
v___x_4799_ = l_Lean_indentD(v___x_4798_);
v___x_4800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4797_);
lean_ctor_set(v___x_4800_, 1, v___x_4799_);
v___x_4801_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4800_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4801_) == 0)
{
lean_dec_ref_known(v___x_4801_, 1);
v_snd_4691_ = v_b_4682_;
goto v___jp_4690_;
}
else
{
lean_object* v_a_4802_; 
v_a_4802_ = lean_ctor_get(v___x_4801_, 0);
lean_inc(v_a_4802_);
lean_dec_ref_known(v___x_4801_, 1);
v_a_4701_ = v_a_4802_;
goto v___jp_4700_;
}
}
else
{
goto v___jp_4791_;
}
}
else
{
goto v___jp_4791_;
}
v___jp_4791_:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4792_ = lean_box(0);
v___x_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4790_);
lean_inc(v_a_4711_);
lean_inc_ref(v_b_4682_);
v___x_4794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4721_, v_b_4682_, v_a_4711_, v___x_4723_, v_only_4677_, v_incremental_4678_, v___x_4792_, v___x_4793_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___x_4721_);
v___y_4705_ = v___x_4794_;
goto v___jp_4704_;
}
}
}
else
{
lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
lean_dec(v___x_4780_);
v___x_4803_ = lean_box(0);
v___x_4804_ = lean_box(0);
lean_inc(v_a_4711_);
lean_inc_ref(v_b_4682_);
v___x_4805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4721_, v_b_4682_, v_a_4711_, v___x_4723_, v_only_4677_, v_incremental_4678_, v___x_4803_, v___x_4804_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___x_4721_);
v___y_4705_ = v___x_4805_;
goto v___jp_4704_;
}
}
}
else
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; uint8_t v___x_4809_; 
v___x_4806_ = lean_unsigned_to_nat(1u);
v___x_4807_ = l_Lean_Syntax_getArg(v___x_4721_, v___x_4806_);
lean_dec(v___x_4721_);
v___x_4808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4807_);
v___x_4809_ = l_Lean_Syntax_isOfKind(v___x_4807_, v___x_4808_);
if (v___x_4809_ == 0)
{
lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
lean_dec(v___x_4807_);
v___x_4810_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4711_);
v___x_4811_ = l_Lean_MessageData_ofSyntax(v_a_4711_);
v___x_4812_ = l_Lean_indentD(v___x_4811_);
v___x_4813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4810_);
lean_ctor_set(v___x_4813_, 1, v___x_4812_);
v___x_4814_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4813_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_dec_ref_known(v___x_4814_, 1);
v_snd_4691_ = v_b_4682_;
goto v___jp_4690_;
}
else
{
lean_object* v_a_4815_; 
v_a_4815_ = lean_ctor_get(v___x_4814_, 0);
lean_inc(v_a_4815_);
lean_dec_ref_known(v___x_4814_, 1);
v_a_4701_ = v_a_4815_;
goto v___jp_4700_;
}
}
else
{
if (v_incremental_4678_ == 0)
{
lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4816_ = lean_box(0);
lean_inc_ref(v_b_4682_);
v___x_4817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4807_, v___x_4713_, v_b_4682_, v___x_4816_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
v___y_4705_ = v___x_4817_;
goto v___jp_4704_;
}
else
{
lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4818_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_4819_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_4711_, v___x_4818_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4819_) == 0)
{
lean_object* v_a_4820_; lean_object* v___x_4821_; 
v_a_4820_ = lean_ctor_get(v___x_4819_, 0);
lean_inc(v_a_4820_);
lean_dec_ref_known(v___x_4819_, 1);
lean_inc_ref(v_b_4682_);
v___x_4821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4807_, v___x_4713_, v_b_4682_, v_a_4820_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
v___y_4705_ = v___x_4821_;
goto v___jp_4704_;
}
else
{
lean_object* v_a_4822_; 
lean_dec(v___x_4807_);
v_a_4822_ = lean_ctor_get(v___x_4819_, 0);
lean_inc(v_a_4822_);
lean_dec_ref_known(v___x_4819_, 1);
v_a_4701_ = v_a_4822_;
goto v___jp_4700_;
}
}
}
}
}
}
v___jp_4690_:
{
size_t v___x_4692_; size_t v___x_4693_; 
v___x_4692_ = ((size_t)1ULL);
v___x_4693_ = lean_usize_add(v_i_4681_, v___x_4692_);
v_i_4681_ = v___x_4693_;
v_b_4682_ = v_snd_4691_;
goto _start;
}
v___jp_4695_:
{
if (v___y_4697_ == 0)
{
if (v_lax_4676_ == 0)
{
lean_object* v___x_4698_; 
lean_dec_ref(v_b_4682_);
v___x_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4698_, 0, v___y_4696_);
return v___x_4698_;
}
else
{
lean_dec_ref(v___y_4696_);
v_snd_4691_ = v_b_4682_;
goto v___jp_4690_;
}
}
else
{
lean_object* v___x_4699_; 
lean_dec_ref(v_b_4682_);
v___x_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4699_, 0, v___y_4696_);
return v___x_4699_;
}
}
v___jp_4700_:
{
uint8_t v___x_4702_; 
v___x_4702_ = l_Lean_Exception_isInterrupt(v_a_4701_);
if (v___x_4702_ == 0)
{
uint8_t v___x_4703_; 
lean_inc_ref(v_a_4701_);
v___x_4703_ = l_Lean_Exception_isRuntime(v_a_4701_);
v___y_4696_ = v_a_4701_;
v___y_4697_ = v___x_4703_;
goto v___jp_4695_;
}
else
{
v___y_4696_ = v_a_4701_;
v___y_4697_ = v___x_4702_;
goto v___jp_4695_;
}
}
v___jp_4704_:
{
if (lean_obj_tag(v___y_4705_) == 0)
{
lean_object* v_a_4706_; lean_object* v_snd_4707_; 
lean_dec_ref(v_b_4682_);
v_a_4706_ = lean_ctor_get(v___y_4705_, 0);
lean_inc(v_a_4706_);
lean_dec_ref_known(v___y_4705_, 1);
v_snd_4707_ = lean_ctor_get(v_a_4706_, 1);
lean_inc(v_snd_4707_);
lean_dec(v_a_4706_);
v_snd_4691_ = v_snd_4707_;
goto v___jp_4690_;
}
else
{
lean_object* v_a_4708_; 
v_a_4708_ = lean_ctor_get(v___y_4705_, 0);
lean_inc(v_a_4708_);
lean_dec_ref_known(v___y_4705_, 1);
v_a_4701_ = v_a_4708_;
goto v___jp_4700_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_4823_, lean_object* v_only_4824_, lean_object* v_incremental_4825_, lean_object* v_as_4826_, lean_object* v_sz_4827_, lean_object* v_i_4828_, lean_object* v_b_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
uint8_t v_lax_boxed_4837_; uint8_t v_only_boxed_4838_; uint8_t v_incremental_boxed_4839_; size_t v_sz_boxed_4840_; size_t v_i_boxed_4841_; lean_object* v_res_4842_; 
v_lax_boxed_4837_ = lean_unbox(v_lax_4823_);
v_only_boxed_4838_ = lean_unbox(v_only_4824_);
v_incremental_boxed_4839_ = lean_unbox(v_incremental_4825_);
v_sz_boxed_4840_ = lean_unbox_usize(v_sz_4827_);
lean_dec(v_sz_4827_);
v_i_boxed_4841_ = lean_unbox_usize(v_i_4828_);
lean_dec(v_i_4828_);
v_res_4842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_4837_, v_only_boxed_4838_, v_incremental_boxed_4839_, v_as_4826_, v_sz_boxed_4840_, v_i_boxed_4841_, v_b_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec_ref(v_as_4826_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_4843_, lean_object* v_ps_4844_, uint8_t v_only_4845_, uint8_t v_lax_4846_, uint8_t v_incremental_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_){
_start:
{
size_t v_sz_4855_; size_t v___x_4856_; lean_object* v___x_4857_; 
v_sz_4855_ = lean_array_size(v_ps_4844_);
v___x_4856_ = ((size_t)0ULL);
v___x_4857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_4846_, v_only_4845_, v_incremental_4847_, v_ps_4844_, v_sz_4855_, v___x_4856_, v_params_4843_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_4858_, lean_object* v_ps_4859_, lean_object* v_only_4860_, lean_object* v_lax_4861_, lean_object* v_incremental_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_){
_start:
{
uint8_t v_only_boxed_4870_; uint8_t v_lax_boxed_4871_; uint8_t v_incremental_boxed_4872_; lean_object* v_res_4873_; 
v_only_boxed_4870_ = lean_unbox(v_only_4860_);
v_lax_boxed_4871_ = lean_unbox(v_lax_4861_);
v_incremental_boxed_4872_ = lean_unbox(v_incremental_4862_);
v_res_4873_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_4858_, v_ps_4859_, v_only_boxed_4870_, v_lax_boxed_4871_, v_incremental_boxed_4872_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
lean_dec(v_a_4868_);
lean_dec_ref(v_a_4867_);
lean_dec(v_a_4866_);
lean_dec_ref(v_a_4865_);
lean_dec(v_a_4864_);
lean_dec_ref(v_a_4863_);
lean_dec_ref(v_ps_4859_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v_origin_4885_; 
v_origin_4885_ = lean_ctor_get(v_thm_4874_, 5);
if (lean_obj_tag(v_origin_4885_) == 0)
{
lean_object* v_declName_4886_; lean_object* v___x_4887_; 
lean_inc_ref(v_origin_4885_);
lean_dec_ref(v_thm_4874_);
v_declName_4886_ = lean_ctor_get(v_origin_4885_, 0);
lean_inc(v_declName_4886_);
lean_dec_ref_known(v_origin_4885_, 1);
v___x_4887_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_4886_, v_a_4882_, v_a_4883_);
return v___x_4887_;
}
else
{
lean_object* v_proof_4888_; lean_object* v___x_4889_; 
v_proof_4888_ = lean_ctor_get(v_thm_4874_, 1);
lean_inc_ref(v_proof_4888_);
lean_dec_ref(v_thm_4874_);
v___x_4889_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_4888_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
return v___x_4889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_){
_start:
{
lean_object* v_res_4901_; 
v_res_4901_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
lean_dec(v_a_4899_);
lean_dec_ref(v_a_4898_);
lean_dec(v_a_4897_);
lean_dec_ref(v_a_4896_);
lean_dec(v_a_4895_);
lean_dec_ref(v_a_4894_);
lean_dec(v_a_4893_);
lean_dec_ref(v_a_4892_);
lean_dec(v_a_4891_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_4902_, size_t v_sz_4903_, size_t v_i_4904_, lean_object* v_b_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_){
_start:
{
uint8_t v___x_4916_; 
v___x_4916_ = lean_usize_dec_lt(v_i_4904_, v_sz_4903_);
if (v___x_4916_ == 0)
{
lean_object* v___x_4917_; 
v___x_4917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4917_, 0, v_b_4905_);
return v___x_4917_;
}
else
{
lean_object* v_snd_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4944_; 
v_snd_4918_ = lean_ctor_get(v_b_4905_, 1);
v_isSharedCheck_4944_ = !lean_is_exclusive(v_b_4905_);
if (v_isSharedCheck_4944_ == 0)
{
lean_object* v_unused_4945_; 
v_unused_4945_ = lean_ctor_get(v_b_4905_, 0);
lean_dec(v_unused_4945_);
v___x_4920_ = v_b_4905_;
v_isShared_4921_ = v_isSharedCheck_4944_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_snd_4918_);
lean_dec(v_b_4905_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4944_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4922_; lean_object* v_a_4924_; lean_object* v_a_4931_; lean_object* v___x_4932_; 
v___x_4922_ = lean_box(0);
v_a_4931_ = lean_array_uget_borrowed(v_as_4902_, v_i_4904_);
lean_inc(v_a_4931_);
v___x_4932_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_4931_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_);
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_a_4933_; uint8_t v___x_4934_; 
v_a_4933_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4933_);
lean_dec_ref_known(v___x_4932_, 1);
v___x_4934_ = lean_unbox(v_a_4933_);
lean_dec(v_a_4933_);
if (v___x_4934_ == 0)
{
v_a_4924_ = v_snd_4918_;
goto v___jp_4923_;
}
else
{
lean_object* v___x_4935_; 
lean_inc(v_a_4931_);
v___x_4935_ = l_Lean_PersistentArray_push___redArg(v_snd_4918_, v_a_4931_);
v_a_4924_ = v___x_4935_;
goto v___jp_4923_;
}
}
else
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
lean_del_object(v___x_4920_);
lean_dec(v_snd_4918_);
v_a_4936_ = lean_ctor_get(v___x_4932_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4932_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4938_ = v___x_4932_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4932_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4936_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
v___jp_4923_:
{
lean_object* v___x_4926_; 
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 1, v_a_4924_);
lean_ctor_set(v___x_4920_, 0, v___x_4922_);
v___x_4926_ = v___x_4920_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4922_);
lean_ctor_set(v_reuseFailAlloc_4930_, 1, v_a_4924_);
v___x_4926_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
size_t v___x_4927_; size_t v___x_4928_; 
v___x_4927_ = ((size_t)1ULL);
v___x_4928_ = lean_usize_add(v_i_4904_, v___x_4927_);
v_i_4904_ = v___x_4928_;
v_b_4905_ = v___x_4926_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4946_, lean_object* v_sz_4947_, lean_object* v_i_4948_, lean_object* v_b_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_){
_start:
{
size_t v_sz_boxed_4960_; size_t v_i_boxed_4961_; lean_object* v_res_4962_; 
v_sz_boxed_4960_ = lean_unbox_usize(v_sz_4947_);
lean_dec(v_sz_4947_);
v_i_boxed_4961_ = lean_unbox_usize(v_i_4948_);
lean_dec(v_i_4948_);
v_res_4962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_4946_, v_sz_boxed_4960_, v_i_boxed_4961_, v_b_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
lean_dec(v___y_4956_);
lean_dec_ref(v___y_4955_);
lean_dec(v___y_4954_);
lean_dec_ref(v___y_4953_);
lean_dec(v___y_4952_);
lean_dec_ref(v___y_4951_);
lean_dec(v___y_4950_);
lean_dec_ref(v_as_4946_);
return v_res_4962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_4963_, size_t v_sz_4964_, size_t v_i_4965_, lean_object* v_b_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
uint8_t v___x_4977_; 
v___x_4977_ = lean_usize_dec_lt(v_i_4965_, v_sz_4964_);
if (v___x_4977_ == 0)
{
lean_object* v___x_4978_; 
v___x_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4978_, 0, v_b_4966_);
return v___x_4978_;
}
else
{
lean_object* v_snd_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_5005_; 
v_snd_4979_ = lean_ctor_get(v_b_4966_, 1);
v_isSharedCheck_5005_ = !lean_is_exclusive(v_b_4966_);
if (v_isSharedCheck_5005_ == 0)
{
lean_object* v_unused_5006_; 
v_unused_5006_ = lean_ctor_get(v_b_4966_, 0);
lean_dec(v_unused_5006_);
v___x_4981_ = v_b_4966_;
v_isShared_4982_ = v_isSharedCheck_5005_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_snd_4979_);
lean_dec(v_b_4966_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_5005_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4983_; lean_object* v_a_4985_; lean_object* v_a_4992_; lean_object* v___x_4993_; 
v___x_4983_ = lean_box(0);
v_a_4992_ = lean_array_uget_borrowed(v_as_4963_, v_i_4965_);
lean_inc(v_a_4992_);
v___x_4993_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_4992_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v_a_4994_; uint8_t v___x_4995_; 
v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
lean_inc(v_a_4994_);
lean_dec_ref_known(v___x_4993_, 1);
v___x_4995_ = lean_unbox(v_a_4994_);
lean_dec(v_a_4994_);
if (v___x_4995_ == 0)
{
v_a_4985_ = v_snd_4979_;
goto v___jp_4984_;
}
else
{
lean_object* v___x_4996_; 
lean_inc(v_a_4992_);
v___x_4996_ = l_Lean_PersistentArray_push___redArg(v_snd_4979_, v_a_4992_);
v_a_4985_ = v___x_4996_;
goto v___jp_4984_;
}
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5004_; 
lean_del_object(v___x_4981_);
lean_dec(v_snd_4979_);
v_a_4997_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4999_ = v___x_4993_;
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4993_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5002_; 
if (v_isShared_5000_ == 0)
{
v___x_5002_ = v___x_4999_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_a_4997_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
v___jp_4984_:
{
lean_object* v___x_4987_; 
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 1, v_a_4985_);
lean_ctor_set(v___x_4981_, 0, v___x_4983_);
v___x_4987_ = v___x_4981_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v___x_4983_);
lean_ctor_set(v_reuseFailAlloc_4991_, 1, v_a_4985_);
v___x_4987_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
size_t v___x_4988_; size_t v___x_4989_; lean_object* v___x_4990_; 
v___x_4988_ = ((size_t)1ULL);
v___x_4989_ = lean_usize_add(v_i_4965_, v___x_4988_);
v___x_4990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_4963_, v_sz_4964_, v___x_4989_, v___x_4987_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
return v___x_4990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5007_, lean_object* v_sz_5008_, lean_object* v_i_5009_, lean_object* v_b_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
size_t v_sz_boxed_5021_; size_t v_i_boxed_5022_; lean_object* v_res_5023_; 
v_sz_boxed_5021_ = lean_unbox_usize(v_sz_5008_);
lean_dec(v_sz_5008_);
v_i_boxed_5022_ = lean_unbox_usize(v_i_5009_);
lean_dec(v_i_5009_);
v_res_5023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5007_, v_sz_boxed_5021_, v_i_boxed_5022_, v_b_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
lean_dec(v___y_5015_);
lean_dec_ref(v___y_5014_);
lean_dec(v___y_5013_);
lean_dec_ref(v___y_5012_);
lean_dec(v___y_5011_);
lean_dec_ref(v_as_5007_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5024_, size_t v_sz_5025_, size_t v_i_5026_, lean_object* v_b_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
uint8_t v___x_5038_; 
v___x_5038_ = lean_usize_dec_lt(v_i_5026_, v_sz_5025_);
if (v___x_5038_ == 0)
{
lean_object* v___x_5039_; 
v___x_5039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5039_, 0, v_b_5027_);
return v___x_5039_;
}
else
{
lean_object* v_snd_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5066_; 
v_snd_5040_ = lean_ctor_get(v_b_5027_, 1);
v_isSharedCheck_5066_ = !lean_is_exclusive(v_b_5027_);
if (v_isSharedCheck_5066_ == 0)
{
lean_object* v_unused_5067_; 
v_unused_5067_ = lean_ctor_get(v_b_5027_, 0);
lean_dec(v_unused_5067_);
v___x_5042_ = v_b_5027_;
v_isShared_5043_ = v_isSharedCheck_5066_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_snd_5040_);
lean_dec(v_b_5027_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5066_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5044_; lean_object* v_a_5046_; lean_object* v_a_5053_; lean_object* v___x_5054_; 
v___x_5044_ = lean_box(0);
v_a_5053_ = lean_array_uget_borrowed(v_as_5024_, v_i_5026_);
lean_inc(v_a_5053_);
v___x_5054_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5053_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_);
if (lean_obj_tag(v___x_5054_) == 0)
{
lean_object* v_a_5055_; uint8_t v___x_5056_; 
v_a_5055_ = lean_ctor_get(v___x_5054_, 0);
lean_inc(v_a_5055_);
lean_dec_ref_known(v___x_5054_, 1);
v___x_5056_ = lean_unbox(v_a_5055_);
lean_dec(v_a_5055_);
if (v___x_5056_ == 0)
{
v_a_5046_ = v_snd_5040_;
goto v___jp_5045_;
}
else
{
lean_object* v___x_5057_; 
lean_inc(v_a_5053_);
v___x_5057_ = l_Lean_PersistentArray_push___redArg(v_snd_5040_, v_a_5053_);
v_a_5046_ = v___x_5057_;
goto v___jp_5045_;
}
}
else
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5065_; 
lean_del_object(v___x_5042_);
lean_dec(v_snd_5040_);
v_a_5058_ = lean_ctor_get(v___x_5054_, 0);
v_isSharedCheck_5065_ = !lean_is_exclusive(v___x_5054_);
if (v_isSharedCheck_5065_ == 0)
{
v___x_5060_ = v___x_5054_;
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_5054_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5061_ == 0)
{
v___x_5063_ = v___x_5060_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
}
v___jp_5045_:
{
lean_object* v___x_5048_; 
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 1, v_a_5046_);
lean_ctor_set(v___x_5042_, 0, v___x_5044_);
v___x_5048_ = v___x_5042_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v___x_5044_);
lean_ctor_set(v_reuseFailAlloc_5052_, 1, v_a_5046_);
v___x_5048_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
size_t v___x_5049_; size_t v___x_5050_; 
v___x_5049_ = ((size_t)1ULL);
v___x_5050_ = lean_usize_add(v_i_5026_, v___x_5049_);
v_i_5026_ = v___x_5050_;
v_b_5027_ = v___x_5048_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5068_, lean_object* v_sz_5069_, lean_object* v_i_5070_, lean_object* v_b_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_){
_start:
{
size_t v_sz_boxed_5082_; size_t v_i_boxed_5083_; lean_object* v_res_5084_; 
v_sz_boxed_5082_ = lean_unbox_usize(v_sz_5069_);
lean_dec(v_sz_5069_);
v_i_boxed_5083_ = lean_unbox_usize(v_i_5070_);
lean_dec(v_i_5070_);
v_res_5084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5068_, v_sz_boxed_5082_, v_i_boxed_5083_, v_b_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec(v___y_5072_);
lean_dec_ref(v_as_5068_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5085_, size_t v_sz_5086_, size_t v_i_5087_, lean_object* v_b_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
uint8_t v___x_5099_; 
v___x_5099_ = lean_usize_dec_lt(v_i_5087_, v_sz_5086_);
if (v___x_5099_ == 0)
{
lean_object* v___x_5100_; 
v___x_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5100_, 0, v_b_5088_);
return v___x_5100_;
}
else
{
lean_object* v_snd_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5127_; 
v_snd_5101_ = lean_ctor_get(v_b_5088_, 1);
v_isSharedCheck_5127_ = !lean_is_exclusive(v_b_5088_);
if (v_isSharedCheck_5127_ == 0)
{
lean_object* v_unused_5128_; 
v_unused_5128_ = lean_ctor_get(v_b_5088_, 0);
lean_dec(v_unused_5128_);
v___x_5103_ = v_b_5088_;
v_isShared_5104_ = v_isSharedCheck_5127_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_snd_5101_);
lean_dec(v_b_5088_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5127_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5105_; lean_object* v_a_5107_; lean_object* v_a_5114_; lean_object* v___x_5115_; 
v___x_5105_ = lean_box(0);
v_a_5114_ = lean_array_uget_borrowed(v_as_5085_, v_i_5087_);
lean_inc(v_a_5114_);
v___x_5115_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5114_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
if (lean_obj_tag(v___x_5115_) == 0)
{
lean_object* v_a_5116_; uint8_t v___x_5117_; 
v_a_5116_ = lean_ctor_get(v___x_5115_, 0);
lean_inc(v_a_5116_);
lean_dec_ref_known(v___x_5115_, 1);
v___x_5117_ = lean_unbox(v_a_5116_);
lean_dec(v_a_5116_);
if (v___x_5117_ == 0)
{
v_a_5107_ = v_snd_5101_;
goto v___jp_5106_;
}
else
{
lean_object* v___x_5118_; 
lean_inc(v_a_5114_);
v___x_5118_ = l_Lean_PersistentArray_push___redArg(v_snd_5101_, v_a_5114_);
v_a_5107_ = v___x_5118_;
goto v___jp_5106_;
}
}
else
{
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
lean_del_object(v___x_5103_);
lean_dec(v_snd_5101_);
v_a_5119_ = lean_ctor_get(v___x_5115_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5115_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5121_ = v___x_5115_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v___x_5115_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5119_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
v___jp_5106_:
{
lean_object* v___x_5109_; 
if (v_isShared_5104_ == 0)
{
lean_ctor_set(v___x_5103_, 1, v_a_5107_);
lean_ctor_set(v___x_5103_, 0, v___x_5105_);
v___x_5109_ = v___x_5103_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5105_);
lean_ctor_set(v_reuseFailAlloc_5113_, 1, v_a_5107_);
v___x_5109_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
size_t v___x_5110_; size_t v___x_5111_; lean_object* v___x_5112_; 
v___x_5110_ = ((size_t)1ULL);
v___x_5111_ = lean_usize_add(v_i_5087_, v___x_5110_);
v___x_5112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5085_, v_sz_5086_, v___x_5111_, v___x_5109_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
return v___x_5112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5129_, lean_object* v_sz_5130_, lean_object* v_i_5131_, lean_object* v_b_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_){
_start:
{
size_t v_sz_boxed_5143_; size_t v_i_boxed_5144_; lean_object* v_res_5145_; 
v_sz_boxed_5143_ = lean_unbox_usize(v_sz_5130_);
lean_dec(v_sz_5130_);
v_i_boxed_5144_ = lean_unbox_usize(v_i_5131_);
lean_dec(v_i_5131_);
v_res_5145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5129_, v_sz_boxed_5143_, v_i_boxed_5144_, v_b_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
lean_dec(v___y_5139_);
lean_dec_ref(v___y_5138_);
lean_dec(v___y_5137_);
lean_dec_ref(v___y_5136_);
lean_dec(v___y_5135_);
lean_dec_ref(v___y_5134_);
lean_dec(v___y_5133_);
lean_dec_ref(v_as_5129_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5146_, lean_object* v_n_5147_, lean_object* v_b_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
if (lean_obj_tag(v_n_5147_) == 0)
{
lean_object* v_cs_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; size_t v_sz_5162_; size_t v___x_5163_; lean_object* v___x_5164_; 
v_cs_5159_ = lean_ctor_get(v_n_5147_, 0);
v___x_5160_ = lean_box(0);
v___x_5161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5160_);
lean_ctor_set(v___x_5161_, 1, v_b_5148_);
v_sz_5162_ = lean_array_size(v_cs_5159_);
v___x_5163_ = ((size_t)0ULL);
v___x_5164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5146_, v_cs_5159_, v_sz_5162_, v___x_5163_, v___x_5161_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5179_; 
v_a_5165_ = lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5164_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5167_ = v___x_5164_;
v_isShared_5168_ = v_isSharedCheck_5179_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5164_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5179_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v_fst_5169_; 
v_fst_5169_ = lean_ctor_get(v_a_5165_, 0);
if (lean_obj_tag(v_fst_5169_) == 0)
{
lean_object* v_snd_5170_; lean_object* v___x_5171_; lean_object* v___x_5173_; 
v_snd_5170_ = lean_ctor_get(v_a_5165_, 1);
lean_inc(v_snd_5170_);
lean_dec(v_a_5165_);
v___x_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5171_, 0, v_snd_5170_);
if (v_isShared_5168_ == 0)
{
lean_ctor_set(v___x_5167_, 0, v___x_5171_);
v___x_5173_ = v___x_5167_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5171_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
}
}
else
{
lean_object* v_val_5175_; lean_object* v___x_5177_; 
lean_inc_ref(v_fst_5169_);
lean_dec(v_a_5165_);
v_val_5175_ = lean_ctor_get(v_fst_5169_, 0);
lean_inc(v_val_5175_);
lean_dec_ref_known(v_fst_5169_, 1);
if (v_isShared_5168_ == 0)
{
lean_ctor_set(v___x_5167_, 0, v_val_5175_);
v___x_5177_ = v___x_5167_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_val_5175_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
}
}
else
{
lean_object* v_a_5180_; lean_object* v___x_5182_; uint8_t v_isShared_5183_; uint8_t v_isSharedCheck_5187_; 
v_a_5180_ = lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5187_ = !lean_is_exclusive(v___x_5164_);
if (v_isSharedCheck_5187_ == 0)
{
v___x_5182_ = v___x_5164_;
v_isShared_5183_ = v_isSharedCheck_5187_;
goto v_resetjp_5181_;
}
else
{
lean_inc(v_a_5180_);
lean_dec(v___x_5164_);
v___x_5182_ = lean_box(0);
v_isShared_5183_ = v_isSharedCheck_5187_;
goto v_resetjp_5181_;
}
v_resetjp_5181_:
{
lean_object* v___x_5185_; 
if (v_isShared_5183_ == 0)
{
v___x_5185_ = v___x_5182_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5186_; 
v_reuseFailAlloc_5186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5186_, 0, v_a_5180_);
v___x_5185_ = v_reuseFailAlloc_5186_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
return v___x_5185_;
}
}
}
}
else
{
lean_object* v_vs_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; size_t v_sz_5191_; size_t v___x_5192_; lean_object* v___x_5193_; 
v_vs_5188_ = lean_ctor_get(v_n_5147_, 0);
v___x_5189_ = lean_box(0);
v___x_5190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5190_, 0, v___x_5189_);
lean_ctor_set(v___x_5190_, 1, v_b_5148_);
v_sz_5191_ = lean_array_size(v_vs_5188_);
v___x_5192_ = ((size_t)0ULL);
v___x_5193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5188_, v_sz_5191_, v___x_5192_, v___x_5190_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5208_; 
v_a_5194_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5208_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5196_ = v___x_5193_;
v_isShared_5197_ = v_isSharedCheck_5208_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5193_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5208_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v_fst_5198_; 
v_fst_5198_ = lean_ctor_get(v_a_5194_, 0);
if (lean_obj_tag(v_fst_5198_) == 0)
{
lean_object* v_snd_5199_; lean_object* v___x_5200_; lean_object* v___x_5202_; 
v_snd_5199_ = lean_ctor_get(v_a_5194_, 1);
lean_inc(v_snd_5199_);
lean_dec(v_a_5194_);
v___x_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5200_, 0, v_snd_5199_);
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 0, v___x_5200_);
v___x_5202_ = v___x_5196_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v___x_5200_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
else
{
lean_object* v_val_5204_; lean_object* v___x_5206_; 
lean_inc_ref(v_fst_5198_);
lean_dec(v_a_5194_);
v_val_5204_ = lean_ctor_get(v_fst_5198_, 0);
lean_inc(v_val_5204_);
lean_dec_ref_known(v_fst_5198_, 1);
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 0, v_val_5204_);
v___x_5206_ = v___x_5196_;
goto v_reusejp_5205_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v_val_5204_);
v___x_5206_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5205_;
}
v_reusejp_5205_:
{
return v___x_5206_;
}
}
}
}
else
{
lean_object* v_a_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5216_; 
v_a_5209_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5216_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5216_ == 0)
{
v___x_5211_ = v___x_5193_;
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_a_5209_);
lean_dec(v___x_5193_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5214_; 
if (v_isShared_5212_ == 0)
{
v___x_5214_ = v___x_5211_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_a_5209_);
v___x_5214_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
return v___x_5214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5217_, lean_object* v_as_5218_, size_t v_sz_5219_, size_t v_i_5220_, lean_object* v_b_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_){
_start:
{
uint8_t v___x_5232_; 
v___x_5232_ = lean_usize_dec_lt(v_i_5220_, v_sz_5219_);
if (v___x_5232_ == 0)
{
lean_object* v___x_5233_; 
v___x_5233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5233_, 0, v_b_5221_);
return v___x_5233_;
}
else
{
lean_object* v_snd_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5268_; 
v_snd_5234_ = lean_ctor_get(v_b_5221_, 1);
v_isSharedCheck_5268_ = !lean_is_exclusive(v_b_5221_);
if (v_isSharedCheck_5268_ == 0)
{
lean_object* v_unused_5269_; 
v_unused_5269_ = lean_ctor_get(v_b_5221_, 0);
lean_dec(v_unused_5269_);
v___x_5236_ = v_b_5221_;
v_isShared_5237_ = v_isSharedCheck_5268_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_snd_5234_);
lean_dec(v_b_5221_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5268_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5238_; lean_object* v_a_5239_; lean_object* v___x_5240_; 
v___x_5238_ = lean_box(0);
v_a_5239_ = lean_array_uget_borrowed(v_as_5218_, v_i_5220_);
lean_inc(v_snd_5234_);
v___x_5240_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5217_, v_a_5239_, v_snd_5234_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_);
if (lean_obj_tag(v___x_5240_) == 0)
{
lean_object* v_a_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5259_; 
v_a_5241_ = lean_ctor_get(v___x_5240_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v___x_5240_);
if (v_isSharedCheck_5259_ == 0)
{
v___x_5243_ = v___x_5240_;
v_isShared_5244_ = v_isSharedCheck_5259_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_a_5241_);
lean_dec(v___x_5240_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5259_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
if (lean_obj_tag(v_a_5241_) == 0)
{
lean_object* v___x_5245_; lean_object* v___x_5247_; 
v___x_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5245_, 0, v_a_5241_);
if (v_isShared_5237_ == 0)
{
lean_ctor_set(v___x_5236_, 0, v___x_5245_);
v___x_5247_ = v___x_5236_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v___x_5245_);
lean_ctor_set(v_reuseFailAlloc_5251_, 1, v_snd_5234_);
v___x_5247_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
lean_object* v___x_5249_; 
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 0, v___x_5247_);
v___x_5249_ = v___x_5243_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v___x_5247_);
v___x_5249_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
return v___x_5249_;
}
}
}
else
{
lean_object* v_a_5252_; lean_object* v___x_5254_; 
lean_del_object(v___x_5243_);
lean_dec(v_snd_5234_);
v_a_5252_ = lean_ctor_get(v_a_5241_, 0);
lean_inc(v_a_5252_);
lean_dec_ref_known(v_a_5241_, 1);
if (v_isShared_5237_ == 0)
{
lean_ctor_set(v___x_5236_, 1, v_a_5252_);
lean_ctor_set(v___x_5236_, 0, v___x_5238_);
v___x_5254_ = v___x_5236_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v___x_5238_);
lean_ctor_set(v_reuseFailAlloc_5258_, 1, v_a_5252_);
v___x_5254_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
size_t v___x_5255_; size_t v___x_5256_; 
v___x_5255_ = ((size_t)1ULL);
v___x_5256_ = lean_usize_add(v_i_5220_, v___x_5255_);
v_i_5220_ = v___x_5256_;
v_b_5221_ = v___x_5254_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5267_; 
lean_del_object(v___x_5236_);
lean_dec(v_snd_5234_);
v_a_5260_ = lean_ctor_get(v___x_5240_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5240_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5262_ = v___x_5240_;
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_a_5260_);
lean_dec(v___x_5240_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
if (v_isShared_5263_ == 0)
{
v___x_5265_ = v___x_5262_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5270_, lean_object* v_as_5271_, lean_object* v_sz_5272_, lean_object* v_i_5273_, lean_object* v_b_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
size_t v_sz_boxed_5285_; size_t v_i_boxed_5286_; lean_object* v_res_5287_; 
v_sz_boxed_5285_ = lean_unbox_usize(v_sz_5272_);
lean_dec(v_sz_5272_);
v_i_boxed_5286_ = lean_unbox_usize(v_i_5273_);
lean_dec(v_i_5273_);
v_res_5287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5270_, v_as_5271_, v_sz_boxed_5285_, v_i_boxed_5286_, v_b_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec(v___y_5275_);
lean_dec_ref(v_as_5271_);
lean_dec_ref(v_init_5270_);
return v_res_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5288_, lean_object* v_n_5289_, lean_object* v_b_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v_res_5301_; 
v_res_5301_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5288_, v_n_5289_, v_b_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec(v___y_5297_);
lean_dec_ref(v___y_5296_);
lean_dec(v___y_5295_);
lean_dec_ref(v___y_5294_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
lean_dec(v___y_5291_);
lean_dec_ref(v_n_5289_);
lean_dec_ref(v_init_5288_);
return v_res_5301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5302_, lean_object* v_init_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_){
_start:
{
lean_object* v_root_5314_; lean_object* v_tail_5315_; lean_object* v___x_5316_; 
v_root_5314_ = lean_ctor_get(v_t_5302_, 0);
v_tail_5315_ = lean_ctor_get(v_t_5302_, 1);
lean_inc_ref(v_init_5303_);
v___x_5316_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5303_, v_root_5314_, v_init_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
lean_dec_ref(v_init_5303_);
if (lean_obj_tag(v___x_5316_) == 0)
{
lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5353_; 
v_a_5317_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5319_ = v___x_5316_;
v_isShared_5320_ = v_isSharedCheck_5353_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_dec(v___x_5316_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5353_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
if (lean_obj_tag(v_a_5317_) == 0)
{
lean_object* v_a_5321_; lean_object* v___x_5323_; 
v_a_5321_ = lean_ctor_get(v_a_5317_, 0);
lean_inc(v_a_5321_);
lean_dec_ref_known(v_a_5317_, 1);
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 0, v_a_5321_);
v___x_5323_ = v___x_5319_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5321_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
else
{
lean_object* v_a_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; size_t v_sz_5328_; size_t v___x_5329_; lean_object* v___x_5330_; 
lean_del_object(v___x_5319_);
v_a_5325_ = lean_ctor_get(v_a_5317_, 0);
lean_inc(v_a_5325_);
lean_dec_ref_known(v_a_5317_, 1);
v___x_5326_ = lean_box(0);
v___x_5327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5326_);
lean_ctor_set(v___x_5327_, 1, v_a_5325_);
v_sz_5328_ = lean_array_size(v_tail_5315_);
v___x_5329_ = ((size_t)0ULL);
v___x_5330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5315_, v_sz_5328_, v___x_5329_, v___x_5327_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
if (lean_obj_tag(v___x_5330_) == 0)
{
lean_object* v_a_5331_; lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5344_; 
v_a_5331_ = lean_ctor_get(v___x_5330_, 0);
v_isSharedCheck_5344_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5344_ == 0)
{
v___x_5333_ = v___x_5330_;
v_isShared_5334_ = v_isSharedCheck_5344_;
goto v_resetjp_5332_;
}
else
{
lean_inc(v_a_5331_);
lean_dec(v___x_5330_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5344_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
lean_object* v_fst_5335_; 
v_fst_5335_ = lean_ctor_get(v_a_5331_, 0);
if (lean_obj_tag(v_fst_5335_) == 0)
{
lean_object* v_snd_5336_; lean_object* v___x_5338_; 
v_snd_5336_ = lean_ctor_get(v_a_5331_, 1);
lean_inc(v_snd_5336_);
lean_dec(v_a_5331_);
if (v_isShared_5334_ == 0)
{
lean_ctor_set(v___x_5333_, 0, v_snd_5336_);
v___x_5338_ = v___x_5333_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_snd_5336_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
else
{
lean_object* v_val_5340_; lean_object* v___x_5342_; 
lean_inc_ref(v_fst_5335_);
lean_dec(v_a_5331_);
v_val_5340_ = lean_ctor_get(v_fst_5335_, 0);
lean_inc(v_val_5340_);
lean_dec_ref_known(v_fst_5335_, 1);
if (v_isShared_5334_ == 0)
{
lean_ctor_set(v___x_5333_, 0, v_val_5340_);
v___x_5342_ = v___x_5333_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v_val_5340_);
v___x_5342_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
return v___x_5342_;
}
}
}
}
else
{
lean_object* v_a_5345_; lean_object* v___x_5347_; uint8_t v_isShared_5348_; uint8_t v_isSharedCheck_5352_; 
v_a_5345_ = lean_ctor_get(v___x_5330_, 0);
v_isSharedCheck_5352_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5352_ == 0)
{
v___x_5347_ = v___x_5330_;
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
else
{
lean_inc(v_a_5345_);
lean_dec(v___x_5330_);
v___x_5347_ = lean_box(0);
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
v_resetjp_5346_:
{
lean_object* v___x_5350_; 
if (v_isShared_5348_ == 0)
{
v___x_5350_ = v___x_5347_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_a_5345_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
}
}
}
}
else
{
lean_object* v_a_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5361_; 
v_a_5354_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5356_ = v___x_5316_;
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
else
{
lean_inc(v_a_5354_);
lean_dec(v___x_5316_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v___x_5359_; 
if (v_isShared_5357_ == 0)
{
v___x_5359_ = v___x_5356_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5354_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5362_, lean_object* v_init_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_){
_start:
{
lean_object* v_res_5374_; 
v_res_5374_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5362_, v_init_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
lean_dec(v___y_5368_);
lean_dec_ref(v___y_5367_);
lean_dec(v___y_5366_);
lean_dec_ref(v___y_5365_);
lean_dec(v___y_5364_);
lean_dec_ref(v_t_5362_);
return v_res_5374_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; 
v___x_5375_ = lean_unsigned_to_nat(32u);
v___x_5376_ = lean_mk_empty_array_with_capacity(v___x_5375_);
v___x_5377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5377_, 0, v___x_5376_);
return v___x_5377_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v_result_5383_; 
v___x_5378_ = ((size_t)5ULL);
v___x_5379_ = lean_unsigned_to_nat(0u);
v___x_5380_ = lean_unsigned_to_nat(32u);
v___x_5381_ = lean_mk_empty_array_with_capacity(v___x_5380_);
v___x_5382_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5383_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5383_, 0, v___x_5382_);
lean_ctor_set(v_result_5383_, 1, v___x_5381_);
lean_ctor_set(v_result_5383_, 2, v___x_5379_);
lean_ctor_set(v_result_5383_, 3, v___x_5379_);
lean_ctor_set_usize(v_result_5383_, 4, v___x_5378_);
return v_result_5383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_){
_start:
{
lean_object* v_result_5395_; lean_object* v___x_5396_; 
v_result_5395_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5396_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5384_, v_result_5395_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_);
return v___x_5396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_){
_start:
{
lean_object* v_res_5408_; 
v_res_5408_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_);
lean_dec(v_a_5406_);
lean_dec_ref(v_a_5405_);
lean_dec(v_a_5404_);
lean_dec_ref(v_a_5403_);
lean_dec(v_a_5402_);
lean_dec_ref(v_a_5401_);
lean_dec(v_a_5400_);
lean_dec_ref(v_a_5399_);
lean_dec(v_a_5398_);
lean_dec_ref(v_thms_5397_);
return v_res_5408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_5411_, lean_object* v_newThms_5412_, lean_object* v_gmt_5413_, lean_object* v_numInstances_5414_, lean_object* v_numDelayedInstances_5415_, lean_object* v_num_5416_, lean_object* v_preInstances_5417_, lean_object* v_nextThmIdx_5418_, lean_object* v_matchEqNames_5419_, lean_object* v_delayedThmInsts_5420_, lean_object* v_nextDeclIdx_5421_, lean_object* v_enodeMap_5422_, lean_object* v_exprs_5423_, lean_object* v_parents_5424_, lean_object* v_congrTable_5425_, lean_object* v_appMap_5426_, lean_object* v_indicesFound_5427_, lean_object* v_newFacts_5428_, uint8_t v_inconsistent_5429_, lean_object* v_nextIdx_5430_, lean_object* v_newRawFacts_5431_, lean_object* v_facts_5432_, lean_object* v_extThms_5433_, lean_object* v_inj_5434_, lean_object* v_split_5435_, lean_object* v_clean_5436_, lean_object* v_sstates_5437_, lean_object* v_mvarId_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_){
_start:
{
lean_object* v___x_5449_; 
v___x_5449_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5411_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
if (lean_obj_tag(v___x_5449_) == 0)
{
lean_object* v_a_5450_; lean_object* v___x_5451_; 
v_a_5450_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_a_5450_);
lean_dec_ref_known(v___x_5449_, 1);
v___x_5451_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_5412_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
if (lean_obj_tag(v___x_5451_) == 0)
{
lean_object* v_a_5452_; lean_object* v___x_5454_; uint8_t v_isShared_5455_; uint8_t v_isSharedCheck_5463_; 
v_a_5452_ = lean_ctor_get(v___x_5451_, 0);
v_isSharedCheck_5463_ = !lean_is_exclusive(v___x_5451_);
if (v_isSharedCheck_5463_ == 0)
{
v___x_5454_ = v___x_5451_;
v_isShared_5455_ = v_isSharedCheck_5463_;
goto v_resetjp_5453_;
}
else
{
lean_inc(v_a_5452_);
lean_dec(v___x_5451_);
v___x_5454_ = lean_box(0);
v_isShared_5455_ = v_isSharedCheck_5463_;
goto v_resetjp_5453_;
}
v_resetjp_5453_:
{
lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5461_; 
v___x_5456_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_5457_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5457_, 0, v___x_5456_);
lean_ctor_set(v___x_5457_, 1, v_gmt_5413_);
lean_ctor_set(v___x_5457_, 2, v_a_5450_);
lean_ctor_set(v___x_5457_, 3, v_a_5452_);
lean_ctor_set(v___x_5457_, 4, v_numInstances_5414_);
lean_ctor_set(v___x_5457_, 5, v_numDelayedInstances_5415_);
lean_ctor_set(v___x_5457_, 6, v_num_5416_);
lean_ctor_set(v___x_5457_, 7, v_preInstances_5417_);
lean_ctor_set(v___x_5457_, 8, v_nextThmIdx_5418_);
lean_ctor_set(v___x_5457_, 9, v_matchEqNames_5419_);
lean_ctor_set(v___x_5457_, 10, v_delayedThmInsts_5420_);
v___x_5458_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_5458_, 0, v_nextDeclIdx_5421_);
lean_ctor_set(v___x_5458_, 1, v_enodeMap_5422_);
lean_ctor_set(v___x_5458_, 2, v_exprs_5423_);
lean_ctor_set(v___x_5458_, 3, v_parents_5424_);
lean_ctor_set(v___x_5458_, 4, v_congrTable_5425_);
lean_ctor_set(v___x_5458_, 5, v_appMap_5426_);
lean_ctor_set(v___x_5458_, 6, v_indicesFound_5427_);
lean_ctor_set(v___x_5458_, 7, v_newFacts_5428_);
lean_ctor_set(v___x_5458_, 8, v_nextIdx_5430_);
lean_ctor_set(v___x_5458_, 9, v_newRawFacts_5431_);
lean_ctor_set(v___x_5458_, 10, v_facts_5432_);
lean_ctor_set(v___x_5458_, 11, v_extThms_5433_);
lean_ctor_set(v___x_5458_, 12, v___x_5457_);
lean_ctor_set(v___x_5458_, 13, v_inj_5434_);
lean_ctor_set(v___x_5458_, 14, v_split_5435_);
lean_ctor_set(v___x_5458_, 15, v_clean_5436_);
lean_ctor_set(v___x_5458_, 16, v_sstates_5437_);
lean_ctor_set_uint8(v___x_5458_, sizeof(void*)*17, v_inconsistent_5429_);
v___x_5459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5459_, 0, v___x_5458_);
lean_ctor_set(v___x_5459_, 1, v_mvarId_5438_);
if (v_isShared_5455_ == 0)
{
lean_ctor_set(v___x_5454_, 0, v___x_5459_);
v___x_5461_ = v___x_5454_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v___x_5459_);
v___x_5461_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
return v___x_5461_;
}
}
}
else
{
lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5471_; 
lean_dec(v_a_5450_);
lean_dec(v_mvarId_5438_);
lean_dec_ref(v_sstates_5437_);
lean_dec_ref(v_clean_5436_);
lean_dec_ref(v_split_5435_);
lean_dec_ref(v_inj_5434_);
lean_dec_ref(v_extThms_5433_);
lean_dec_ref(v_facts_5432_);
lean_dec_ref(v_newRawFacts_5431_);
lean_dec(v_nextIdx_5430_);
lean_dec_ref(v_newFacts_5428_);
lean_dec_ref(v_indicesFound_5427_);
lean_dec_ref(v_appMap_5426_);
lean_dec_ref(v_congrTable_5425_);
lean_dec_ref(v_parents_5424_);
lean_dec_ref(v_exprs_5423_);
lean_dec_ref(v_enodeMap_5422_);
lean_dec(v_nextDeclIdx_5421_);
lean_dec_ref(v_delayedThmInsts_5420_);
lean_dec_ref(v_matchEqNames_5419_);
lean_dec(v_nextThmIdx_5418_);
lean_dec_ref(v_preInstances_5417_);
lean_dec(v_num_5416_);
lean_dec(v_numDelayedInstances_5415_);
lean_dec(v_numInstances_5414_);
lean_dec(v_gmt_5413_);
v_a_5464_ = lean_ctor_get(v___x_5451_, 0);
v_isSharedCheck_5471_ = !lean_is_exclusive(v___x_5451_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5466_ = v___x_5451_;
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_dec(v___x_5451_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5469_; 
if (v_isShared_5467_ == 0)
{
v___x_5469_ = v___x_5466_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5464_);
v___x_5469_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
return v___x_5469_;
}
}
}
}
else
{
lean_object* v_a_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5479_; 
lean_dec(v_mvarId_5438_);
lean_dec_ref(v_sstates_5437_);
lean_dec_ref(v_clean_5436_);
lean_dec_ref(v_split_5435_);
lean_dec_ref(v_inj_5434_);
lean_dec_ref(v_extThms_5433_);
lean_dec_ref(v_facts_5432_);
lean_dec_ref(v_newRawFacts_5431_);
lean_dec(v_nextIdx_5430_);
lean_dec_ref(v_newFacts_5428_);
lean_dec_ref(v_indicesFound_5427_);
lean_dec_ref(v_appMap_5426_);
lean_dec_ref(v_congrTable_5425_);
lean_dec_ref(v_parents_5424_);
lean_dec_ref(v_exprs_5423_);
lean_dec_ref(v_enodeMap_5422_);
lean_dec(v_nextDeclIdx_5421_);
lean_dec_ref(v_delayedThmInsts_5420_);
lean_dec_ref(v_matchEqNames_5419_);
lean_dec(v_nextThmIdx_5418_);
lean_dec_ref(v_preInstances_5417_);
lean_dec(v_num_5416_);
lean_dec(v_numDelayedInstances_5415_);
lean_dec(v_numInstances_5414_);
lean_dec(v_gmt_5413_);
v_a_5472_ = lean_ctor_get(v___x_5449_, 0);
v_isSharedCheck_5479_ = !lean_is_exclusive(v___x_5449_);
if (v_isSharedCheck_5479_ == 0)
{
v___x_5474_ = v___x_5449_;
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_a_5472_);
lean_dec(v___x_5449_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v___x_5477_; 
if (v_isShared_5475_ == 0)
{
v___x_5477_ = v___x_5474_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v_a_5472_);
v___x_5477_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
return v___x_5477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_5480_ = _args[0];
lean_object* v_newThms_5481_ = _args[1];
lean_object* v_gmt_5482_ = _args[2];
lean_object* v_numInstances_5483_ = _args[3];
lean_object* v_numDelayedInstances_5484_ = _args[4];
lean_object* v_num_5485_ = _args[5];
lean_object* v_preInstances_5486_ = _args[6];
lean_object* v_nextThmIdx_5487_ = _args[7];
lean_object* v_matchEqNames_5488_ = _args[8];
lean_object* v_delayedThmInsts_5489_ = _args[9];
lean_object* v_nextDeclIdx_5490_ = _args[10];
lean_object* v_enodeMap_5491_ = _args[11];
lean_object* v_exprs_5492_ = _args[12];
lean_object* v_parents_5493_ = _args[13];
lean_object* v_congrTable_5494_ = _args[14];
lean_object* v_appMap_5495_ = _args[15];
lean_object* v_indicesFound_5496_ = _args[16];
lean_object* v_newFacts_5497_ = _args[17];
lean_object* v_inconsistent_5498_ = _args[18];
lean_object* v_nextIdx_5499_ = _args[19];
lean_object* v_newRawFacts_5500_ = _args[20];
lean_object* v_facts_5501_ = _args[21];
lean_object* v_extThms_5502_ = _args[22];
lean_object* v_inj_5503_ = _args[23];
lean_object* v_split_5504_ = _args[24];
lean_object* v_clean_5505_ = _args[25];
lean_object* v_sstates_5506_ = _args[26];
lean_object* v_mvarId_5507_ = _args[27];
lean_object* v___y_5508_ = _args[28];
lean_object* v___y_5509_ = _args[29];
lean_object* v___y_5510_ = _args[30];
lean_object* v___y_5511_ = _args[31];
lean_object* v___y_5512_ = _args[32];
lean_object* v___y_5513_ = _args[33];
lean_object* v___y_5514_ = _args[34];
lean_object* v___y_5515_ = _args[35];
lean_object* v___y_5516_ = _args[36];
lean_object* v___y_5517_ = _args[37];
_start:
{
uint8_t v_inconsistent_boxed_5518_; lean_object* v_res_5519_; 
v_inconsistent_boxed_5518_ = lean_unbox(v_inconsistent_5498_);
v_res_5519_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5480_, v_newThms_5481_, v_gmt_5482_, v_numInstances_5483_, v_numDelayedInstances_5484_, v_num_5485_, v_preInstances_5486_, v_nextThmIdx_5487_, v_matchEqNames_5488_, v_delayedThmInsts_5489_, v_nextDeclIdx_5490_, v_enodeMap_5491_, v_exprs_5492_, v_parents_5493_, v_congrTable_5494_, v_appMap_5495_, v_indicesFound_5496_, v_newFacts_5497_, v_inconsistent_boxed_5518_, v_nextIdx_5499_, v_newRawFacts_5500_, v_facts_5501_, v_extThms_5502_, v_inj_5503_, v_split_5504_, v_clean_5505_, v_sstates_5506_, v_mvarId_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_);
lean_dec(v___y_5516_);
lean_dec_ref(v___y_5515_);
lean_dec(v___y_5514_);
lean_dec_ref(v___y_5513_);
lean_dec(v___y_5512_);
lean_dec_ref(v___y_5511_);
lean_dec(v___y_5510_);
lean_dec_ref(v___y_5509_);
lean_dec(v___y_5508_);
lean_dec_ref(v_newThms_5481_);
lean_dec_ref(v_thms_5480_);
return v_res_5519_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5520_; 
v___x_5520_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_5520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_5521_, size_t v_i_5522_, lean_object* v_bs_5523_){
_start:
{
uint8_t v___x_5524_; 
v___x_5524_ = lean_usize_dec_lt(v_i_5522_, v_sz_5521_);
if (v___x_5524_ == 0)
{
return v_bs_5523_;
}
else
{
lean_object* v_v_5525_; lean_object* v_casesTypes_5526_; lean_object* v_extThms_5527_; lean_object* v_funCC_5528_; lean_object* v_inj_5529_; lean_object* v___x_5531_; uint8_t v_isShared_5532_; uint8_t v_isSharedCheck_5543_; 
v_v_5525_ = lean_array_uget(v_bs_5523_, v_i_5522_);
v_casesTypes_5526_ = lean_ctor_get(v_v_5525_, 0);
v_extThms_5527_ = lean_ctor_get(v_v_5525_, 1);
v_funCC_5528_ = lean_ctor_get(v_v_5525_, 2);
v_inj_5529_ = lean_ctor_get(v_v_5525_, 4);
v_isSharedCheck_5543_ = !lean_is_exclusive(v_v_5525_);
if (v_isSharedCheck_5543_ == 0)
{
lean_object* v_unused_5544_; 
v_unused_5544_ = lean_ctor_get(v_v_5525_, 3);
lean_dec(v_unused_5544_);
v___x_5531_ = v_v_5525_;
v_isShared_5532_ = v_isSharedCheck_5543_;
goto v_resetjp_5530_;
}
else
{
lean_inc(v_inj_5529_);
lean_inc(v_funCC_5528_);
lean_inc(v_extThms_5527_);
lean_inc(v_casesTypes_5526_);
lean_dec(v_v_5525_);
v___x_5531_ = lean_box(0);
v_isShared_5532_ = v_isSharedCheck_5543_;
goto v_resetjp_5530_;
}
v_resetjp_5530_:
{
lean_object* v___x_5533_; lean_object* v_bs_x27_5534_; lean_object* v___x_5535_; lean_object* v___x_5537_; 
v___x_5533_ = lean_unsigned_to_nat(0u);
v_bs_x27_5534_ = lean_array_uset(v_bs_5523_, v_i_5522_, v___x_5533_);
v___x_5535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_5532_ == 0)
{
lean_ctor_set(v___x_5531_, 3, v___x_5535_);
v___x_5537_ = v___x_5531_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_casesTypes_5526_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v_extThms_5527_);
lean_ctor_set(v_reuseFailAlloc_5542_, 2, v_funCC_5528_);
lean_ctor_set(v_reuseFailAlloc_5542_, 3, v___x_5535_);
lean_ctor_set(v_reuseFailAlloc_5542_, 4, v_inj_5529_);
v___x_5537_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
size_t v___x_5538_; size_t v___x_5539_; lean_object* v___x_5540_; 
v___x_5538_ = ((size_t)1ULL);
v___x_5539_ = lean_usize_add(v_i_5522_, v___x_5538_);
v___x_5540_ = lean_array_uset(v_bs_x27_5534_, v_i_5522_, v___x_5537_);
v_i_5522_ = v___x_5539_;
v_bs_5523_ = v___x_5540_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_5545_, lean_object* v_i_5546_, lean_object* v_bs_5547_){
_start:
{
size_t v_sz_boxed_5548_; size_t v_i_boxed_5549_; lean_object* v_res_5550_; 
v_sz_boxed_5548_ = lean_unbox_usize(v_sz_5545_);
lean_dec(v_sz_5545_);
v_i_boxed_5549_ = lean_unbox_usize(v_i_5546_);
lean_dec(v_i_5546_);
v_res_5550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_5548_, v_i_boxed_5549_, v_bs_5547_);
return v_res_5550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_5551_, lean_object* v_ps_5552_, uint8_t v_only_5553_, lean_object* v_k_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_, lean_object* v_a_5562_){
_start:
{
lean_object* v___y_5565_; lean_object* v___y_5566_; lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___y_5569_; lean_object* v___y_5570_; lean_object* v___y_5571_; lean_object* v___y_5572_; lean_object* v___y_5573_; uint8_t v___y_5586_; uint8_t v___y_5587_; lean_object* v_params_5588_; lean_object* v___y_5589_; lean_object* v___y_5590_; lean_object* v___y_5591_; lean_object* v___y_5592_; lean_object* v___y_5593_; lean_object* v___y_5594_; lean_object* v___y_5595_; lean_object* v___y_5596_; uint8_t v___y_5697_; 
if (v_only_5553_ == 0)
{
lean_object* v___x_5719_; lean_object* v___x_5720_; uint8_t v___x_5721_; 
v___x_5719_ = lean_array_get_size(v_ps_5552_);
v___x_5720_ = lean_unsigned_to_nat(0u);
v___x_5721_ = lean_nat_dec_eq(v___x_5719_, v___x_5720_);
if (v___x_5721_ == 0)
{
v___y_5697_ = v___x_5721_;
goto v___jp_5696_;
}
else
{
lean_object* v___x_5722_; 
lean_dec_ref(v_params_5551_);
lean_inc(v_a_5562_);
lean_inc_ref(v_a_5561_);
lean_inc(v_a_5560_);
lean_inc_ref(v_a_5559_);
lean_inc(v_a_5558_);
lean_inc_ref(v_a_5557_);
lean_inc(v_a_5556_);
lean_inc_ref(v_a_5555_);
v___x_5722_ = lean_apply_9(v_k_5554_, v_a_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, lean_box(0));
return v___x_5722_;
}
}
else
{
uint8_t v___x_5723_; 
v___x_5723_ = 0;
v___y_5697_ = v___x_5723_;
goto v___jp_5696_;
}
v___jp_5564_:
{
lean_object* v___x_5574_; lean_object* v___x_5575_; 
v___x_5574_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_5574_, 0, v___y_5565_);
v___x_5575_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_5574_, v___y_5566_, v___y_5567_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_object* v___x_5576_; 
lean_dec_ref_known(v___x_5575_, 1);
lean_inc(v___y_5573_);
lean_inc_ref(v___y_5572_);
lean_inc(v___y_5571_);
lean_inc_ref(v___y_5570_);
lean_inc(v___y_5569_);
lean_inc_ref(v___y_5568_);
lean_inc(v___y_5567_);
v___x_5576_ = lean_apply_9(v_k_5554_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, lean_box(0));
return v___x_5576_;
}
else
{
lean_object* v_a_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5584_; 
lean_dec_ref(v___y_5566_);
lean_dec_ref(v_k_5554_);
v_a_5577_ = lean_ctor_get(v___x_5575_, 0);
v_isSharedCheck_5584_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5584_ == 0)
{
v___x_5579_ = v___x_5575_;
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_a_5577_);
lean_dec(v___x_5575_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5582_; 
if (v_isShared_5580_ == 0)
{
v___x_5582_ = v___x_5579_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_a_5577_);
v___x_5582_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
return v___x_5582_;
}
}
}
}
v___jp_5585_:
{
lean_object* v___x_5597_; 
v___x_5597_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5588_, v_ps_5552_, v_only_5553_, v___y_5586_, v___y_5587_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_);
if (lean_obj_tag(v___x_5597_) == 0)
{
lean_object* v_a_5598_; lean_object* v_ctx_5599_; lean_object* v_anchorRefs_x3f_5600_; lean_object* v_toContext_5601_; lean_object* v_sctx_5602_; lean_object* v_methods_5603_; uint8_t v_sym_5604_; lean_object* v_simp_5605_; lean_object* v_simpMethods_5606_; lean_object* v_config_5607_; uint8_t v_cheapCases_5608_; uint8_t v_reportMVarIssue_5609_; lean_object* v_splitSource_5610_; lean_object* v_ematchDiagSource_5611_; lean_object* v_symPrios_5612_; lean_object* v_extensions_5613_; uint8_t v_debug_5614_; uint8_t v_ematchDiag_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; 
v_a_5598_ = lean_ctor_get(v___x_5597_, 0);
lean_inc_n(v_a_5598_, 2);
lean_dec_ref_known(v___x_5597_, 1);
v_ctx_5599_ = lean_ctor_get(v___y_5589_, 1);
v_anchorRefs_x3f_5600_ = lean_ctor_get(v_a_5598_, 8);
v_toContext_5601_ = lean_ctor_get(v___y_5589_, 0);
v_sctx_5602_ = lean_ctor_get(v___y_5589_, 2);
v_methods_5603_ = lean_ctor_get(v___y_5589_, 3);
v_sym_5604_ = lean_ctor_get_uint8(v___y_5589_, sizeof(void*)*5);
v_simp_5605_ = lean_ctor_get(v_ctx_5599_, 0);
v_simpMethods_5606_ = lean_ctor_get(v_ctx_5599_, 1);
v_config_5607_ = lean_ctor_get(v_ctx_5599_, 2);
v_cheapCases_5608_ = lean_ctor_get_uint8(v_ctx_5599_, sizeof(void*)*8);
v_reportMVarIssue_5609_ = lean_ctor_get_uint8(v_ctx_5599_, sizeof(void*)*8 + 1);
v_splitSource_5610_ = lean_ctor_get(v_ctx_5599_, 4);
v_ematchDiagSource_5611_ = lean_ctor_get(v_ctx_5599_, 5);
v_symPrios_5612_ = lean_ctor_get(v_ctx_5599_, 6);
v_extensions_5613_ = lean_ctor_get(v_ctx_5599_, 7);
v_debug_5614_ = lean_ctor_get_uint8(v_ctx_5599_, sizeof(void*)*8 + 2);
v_ematchDiag_5615_ = lean_ctor_get_uint8(v_ctx_5599_, sizeof(void*)*8 + 3);
lean_inc_ref(v_extensions_5613_);
lean_inc_ref(v_symPrios_5612_);
lean_inc(v_ematchDiagSource_5611_);
lean_inc(v_splitSource_5610_);
lean_inc(v_anchorRefs_x3f_5600_);
lean_inc_ref(v_config_5607_);
lean_inc_ref(v_simpMethods_5606_);
lean_inc_ref(v_simp_5605_);
v___x_5616_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_5616_, 0, v_simp_5605_);
lean_ctor_set(v___x_5616_, 1, v_simpMethods_5606_);
lean_ctor_set(v___x_5616_, 2, v_config_5607_);
lean_ctor_set(v___x_5616_, 3, v_anchorRefs_x3f_5600_);
lean_ctor_set(v___x_5616_, 4, v_splitSource_5610_);
lean_ctor_set(v___x_5616_, 5, v_ematchDiagSource_5611_);
lean_ctor_set(v___x_5616_, 6, v_symPrios_5612_);
lean_ctor_set(v___x_5616_, 7, v_extensions_5613_);
lean_ctor_set_uint8(v___x_5616_, sizeof(void*)*8, v_cheapCases_5608_);
lean_ctor_set_uint8(v___x_5616_, sizeof(void*)*8 + 1, v_reportMVarIssue_5609_);
lean_ctor_set_uint8(v___x_5616_, sizeof(void*)*8 + 2, v_debug_5614_);
lean_ctor_set_uint8(v___x_5616_, sizeof(void*)*8 + 3, v_ematchDiag_5615_);
lean_inc_ref(v_methods_5603_);
lean_inc_ref(v_sctx_5602_);
lean_inc_ref(v_toContext_5601_);
v___x_5617_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_5617_, 0, v_toContext_5601_);
lean_ctor_set(v___x_5617_, 1, v___x_5616_);
lean_ctor_set(v___x_5617_, 2, v_sctx_5602_);
lean_ctor_set(v___x_5617_, 3, v_methods_5603_);
lean_ctor_set(v___x_5617_, 4, v_a_5598_);
lean_ctor_set_uint8(v___x_5617_, sizeof(void*)*5, v_sym_5604_);
if (v_only_5553_ == 0)
{
v___y_5565_ = v_a_5598_;
v___y_5566_ = v___x_5617_;
v___y_5567_ = v___y_5590_;
v___y_5568_ = v___y_5591_;
v___y_5569_ = v___y_5592_;
v___y_5570_ = v___y_5593_;
v___y_5571_ = v___y_5594_;
v___y_5572_ = v___y_5595_;
v___y_5573_ = v___y_5596_;
goto v___jp_5564_;
}
else
{
lean_object* v___x_5618_; 
v___x_5618_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_5590_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_);
if (lean_obj_tag(v___x_5618_) == 0)
{
lean_object* v_a_5619_; lean_object* v_toGoalState_5620_; lean_object* v_ematch_5621_; lean_object* v_mvarId_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5678_; 
v_a_5619_ = lean_ctor_get(v___x_5618_, 0);
lean_inc(v_a_5619_);
lean_dec_ref_known(v___x_5618_, 1);
v_toGoalState_5620_ = lean_ctor_get(v_a_5619_, 0);
lean_inc_ref(v_toGoalState_5620_);
v_ematch_5621_ = lean_ctor_get(v_toGoalState_5620_, 12);
lean_inc_ref(v_ematch_5621_);
v_mvarId_5622_ = lean_ctor_get(v_a_5619_, 1);
v_isSharedCheck_5678_ = !lean_is_exclusive(v_a_5619_);
if (v_isSharedCheck_5678_ == 0)
{
lean_object* v_unused_5679_; 
v_unused_5679_ = lean_ctor_get(v_a_5619_, 0);
lean_dec(v_unused_5679_);
v___x_5624_ = v_a_5619_;
v_isShared_5625_ = v_isSharedCheck_5678_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_mvarId_5622_);
lean_dec(v_a_5619_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5678_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
lean_object* v_nextDeclIdx_5626_; lean_object* v_enodeMap_5627_; lean_object* v_exprs_5628_; lean_object* v_parents_5629_; lean_object* v_congrTable_5630_; lean_object* v_appMap_5631_; lean_object* v_indicesFound_5632_; lean_object* v_newFacts_5633_; uint8_t v_inconsistent_5634_; lean_object* v_nextIdx_5635_; lean_object* v_newRawFacts_5636_; lean_object* v_facts_5637_; lean_object* v_extThms_5638_; lean_object* v_inj_5639_; lean_object* v_split_5640_; lean_object* v_clean_5641_; lean_object* v_sstates_5642_; lean_object* v_gmt_5643_; lean_object* v_thms_5644_; lean_object* v_newThms_5645_; lean_object* v_numInstances_5646_; lean_object* v_numDelayedInstances_5647_; lean_object* v_num_5648_; lean_object* v_preInstances_5649_; lean_object* v_nextThmIdx_5650_; lean_object* v_matchEqNames_5651_; lean_object* v_delayedThmInsts_5652_; lean_object* v___x_5653_; lean_object* v___f_5654_; lean_object* v___x_5655_; 
v_nextDeclIdx_5626_ = lean_ctor_get(v_toGoalState_5620_, 0);
lean_inc(v_nextDeclIdx_5626_);
v_enodeMap_5627_ = lean_ctor_get(v_toGoalState_5620_, 1);
lean_inc_ref(v_enodeMap_5627_);
v_exprs_5628_ = lean_ctor_get(v_toGoalState_5620_, 2);
lean_inc_ref(v_exprs_5628_);
v_parents_5629_ = lean_ctor_get(v_toGoalState_5620_, 3);
lean_inc_ref(v_parents_5629_);
v_congrTable_5630_ = lean_ctor_get(v_toGoalState_5620_, 4);
lean_inc_ref(v_congrTable_5630_);
v_appMap_5631_ = lean_ctor_get(v_toGoalState_5620_, 5);
lean_inc_ref(v_appMap_5631_);
v_indicesFound_5632_ = lean_ctor_get(v_toGoalState_5620_, 6);
lean_inc_ref(v_indicesFound_5632_);
v_newFacts_5633_ = lean_ctor_get(v_toGoalState_5620_, 7);
lean_inc_ref(v_newFacts_5633_);
v_inconsistent_5634_ = lean_ctor_get_uint8(v_toGoalState_5620_, sizeof(void*)*17);
v_nextIdx_5635_ = lean_ctor_get(v_toGoalState_5620_, 8);
lean_inc(v_nextIdx_5635_);
v_newRawFacts_5636_ = lean_ctor_get(v_toGoalState_5620_, 9);
lean_inc_ref(v_newRawFacts_5636_);
v_facts_5637_ = lean_ctor_get(v_toGoalState_5620_, 10);
lean_inc_ref(v_facts_5637_);
v_extThms_5638_ = lean_ctor_get(v_toGoalState_5620_, 11);
lean_inc_ref(v_extThms_5638_);
v_inj_5639_ = lean_ctor_get(v_toGoalState_5620_, 13);
lean_inc_ref(v_inj_5639_);
v_split_5640_ = lean_ctor_get(v_toGoalState_5620_, 14);
lean_inc_ref(v_split_5640_);
v_clean_5641_ = lean_ctor_get(v_toGoalState_5620_, 15);
lean_inc_ref(v_clean_5641_);
v_sstates_5642_ = lean_ctor_get(v_toGoalState_5620_, 16);
lean_inc_ref(v_sstates_5642_);
lean_dec_ref(v_toGoalState_5620_);
v_gmt_5643_ = lean_ctor_get(v_ematch_5621_, 1);
lean_inc(v_gmt_5643_);
v_thms_5644_ = lean_ctor_get(v_ematch_5621_, 2);
lean_inc_ref(v_thms_5644_);
v_newThms_5645_ = lean_ctor_get(v_ematch_5621_, 3);
lean_inc_ref(v_newThms_5645_);
v_numInstances_5646_ = lean_ctor_get(v_ematch_5621_, 4);
lean_inc(v_numInstances_5646_);
v_numDelayedInstances_5647_ = lean_ctor_get(v_ematch_5621_, 5);
lean_inc(v_numDelayedInstances_5647_);
v_num_5648_ = lean_ctor_get(v_ematch_5621_, 6);
lean_inc(v_num_5648_);
v_preInstances_5649_ = lean_ctor_get(v_ematch_5621_, 7);
lean_inc_ref(v_preInstances_5649_);
v_nextThmIdx_5650_ = lean_ctor_get(v_ematch_5621_, 8);
lean_inc(v_nextThmIdx_5650_);
v_matchEqNames_5651_ = lean_ctor_get(v_ematch_5621_, 9);
lean_inc_ref(v_matchEqNames_5651_);
v_delayedThmInsts_5652_ = lean_ctor_get(v_ematch_5621_, 10);
lean_inc_ref(v_delayedThmInsts_5652_);
lean_dec_ref(v_ematch_5621_);
v___x_5653_ = lean_box(v_inconsistent_5634_);
v___f_5654_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 38, 28);
lean_closure_set(v___f_5654_, 0, v_thms_5644_);
lean_closure_set(v___f_5654_, 1, v_newThms_5645_);
lean_closure_set(v___f_5654_, 2, v_gmt_5643_);
lean_closure_set(v___f_5654_, 3, v_numInstances_5646_);
lean_closure_set(v___f_5654_, 4, v_numDelayedInstances_5647_);
lean_closure_set(v___f_5654_, 5, v_num_5648_);
lean_closure_set(v___f_5654_, 6, v_preInstances_5649_);
lean_closure_set(v___f_5654_, 7, v_nextThmIdx_5650_);
lean_closure_set(v___f_5654_, 8, v_matchEqNames_5651_);
lean_closure_set(v___f_5654_, 9, v_delayedThmInsts_5652_);
lean_closure_set(v___f_5654_, 10, v_nextDeclIdx_5626_);
lean_closure_set(v___f_5654_, 11, v_enodeMap_5627_);
lean_closure_set(v___f_5654_, 12, v_exprs_5628_);
lean_closure_set(v___f_5654_, 13, v_parents_5629_);
lean_closure_set(v___f_5654_, 14, v_congrTable_5630_);
lean_closure_set(v___f_5654_, 15, v_appMap_5631_);
lean_closure_set(v___f_5654_, 16, v_indicesFound_5632_);
lean_closure_set(v___f_5654_, 17, v_newFacts_5633_);
lean_closure_set(v___f_5654_, 18, v___x_5653_);
lean_closure_set(v___f_5654_, 19, v_nextIdx_5635_);
lean_closure_set(v___f_5654_, 20, v_newRawFacts_5636_);
lean_closure_set(v___f_5654_, 21, v_facts_5637_);
lean_closure_set(v___f_5654_, 22, v_extThms_5638_);
lean_closure_set(v___f_5654_, 23, v_inj_5639_);
lean_closure_set(v___f_5654_, 24, v_split_5640_);
lean_closure_set(v___f_5654_, 25, v_clean_5641_);
lean_closure_set(v___f_5654_, 26, v_sstates_5642_);
lean_closure_set(v___f_5654_, 27, v_mvarId_5622_);
v___x_5655_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_5654_, v___x_5617_, v___y_5590_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_);
if (lean_obj_tag(v___x_5655_) == 0)
{
lean_object* v_a_5656_; lean_object* v___x_5657_; lean_object* v___x_5659_; 
v_a_5656_ = lean_ctor_get(v___x_5655_, 0);
lean_inc(v_a_5656_);
lean_dec_ref_known(v___x_5655_, 1);
v___x_5657_ = lean_box(0);
if (v_isShared_5625_ == 0)
{
lean_ctor_set_tag(v___x_5624_, 1);
lean_ctor_set(v___x_5624_, 1, v___x_5657_);
lean_ctor_set(v___x_5624_, 0, v_a_5656_);
v___x_5659_ = v___x_5624_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5656_);
lean_ctor_set(v_reuseFailAlloc_5669_, 1, v___x_5657_);
v___x_5659_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
lean_object* v___x_5660_; 
v___x_5660_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_5659_, v___y_5590_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_);
if (lean_obj_tag(v___x_5660_) == 0)
{
lean_dec_ref_known(v___x_5660_, 1);
v___y_5565_ = v_a_5598_;
v___y_5566_ = v___x_5617_;
v___y_5567_ = v___y_5590_;
v___y_5568_ = v___y_5591_;
v___y_5569_ = v___y_5592_;
v___y_5570_ = v___y_5593_;
v___y_5571_ = v___y_5594_;
v___y_5572_ = v___y_5595_;
v___y_5573_ = v___y_5596_;
goto v___jp_5564_;
}
else
{
lean_object* v_a_5661_; lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5668_; 
lean_dec_ref_known(v___x_5617_, 5);
lean_dec(v_a_5598_);
lean_dec_ref(v_k_5554_);
v_a_5661_ = lean_ctor_get(v___x_5660_, 0);
v_isSharedCheck_5668_ = !lean_is_exclusive(v___x_5660_);
if (v_isSharedCheck_5668_ == 0)
{
v___x_5663_ = v___x_5660_;
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
else
{
lean_inc(v_a_5661_);
lean_dec(v___x_5660_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
lean_object* v___x_5666_; 
if (v_isShared_5664_ == 0)
{
v___x_5666_ = v___x_5663_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_a_5661_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
}
}
else
{
lean_object* v_a_5670_; lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5677_; 
lean_del_object(v___x_5624_);
lean_dec_ref_known(v___x_5617_, 5);
lean_dec(v_a_5598_);
lean_dec_ref(v_k_5554_);
v_a_5670_ = lean_ctor_get(v___x_5655_, 0);
v_isSharedCheck_5677_ = !lean_is_exclusive(v___x_5655_);
if (v_isSharedCheck_5677_ == 0)
{
v___x_5672_ = v___x_5655_;
v_isShared_5673_ = v_isSharedCheck_5677_;
goto v_resetjp_5671_;
}
else
{
lean_inc(v_a_5670_);
lean_dec(v___x_5655_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5677_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
lean_object* v___x_5675_; 
if (v_isShared_5673_ == 0)
{
v___x_5675_ = v___x_5672_;
goto v_reusejp_5674_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_a_5670_);
v___x_5675_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5674_;
}
v_reusejp_5674_:
{
return v___x_5675_;
}
}
}
}
}
else
{
lean_object* v_a_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5687_; 
lean_dec_ref_known(v___x_5617_, 5);
lean_dec(v_a_5598_);
lean_dec_ref(v_k_5554_);
v_a_5680_ = lean_ctor_get(v___x_5618_, 0);
v_isSharedCheck_5687_ = !lean_is_exclusive(v___x_5618_);
if (v_isSharedCheck_5687_ == 0)
{
v___x_5682_ = v___x_5618_;
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_a_5680_);
lean_dec(v___x_5618_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
lean_object* v___x_5685_; 
if (v_isShared_5683_ == 0)
{
v___x_5685_ = v___x_5682_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v_a_5680_);
v___x_5685_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
return v___x_5685_;
}
}
}
}
}
else
{
lean_object* v_a_5688_; lean_object* v___x_5690_; uint8_t v_isShared_5691_; uint8_t v_isSharedCheck_5695_; 
lean_dec_ref(v_k_5554_);
v_a_5688_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5695_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5690_ = v___x_5597_;
v_isShared_5691_ = v_isSharedCheck_5695_;
goto v_resetjp_5689_;
}
else
{
lean_inc(v_a_5688_);
lean_dec(v___x_5597_);
v___x_5690_ = lean_box(0);
v_isShared_5691_ = v_isSharedCheck_5695_;
goto v_resetjp_5689_;
}
v_resetjp_5689_:
{
lean_object* v___x_5693_; 
if (v_isShared_5691_ == 0)
{
v___x_5693_ = v___x_5690_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_a_5688_);
v___x_5693_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
return v___x_5693_;
}
}
}
}
v___jp_5696_:
{
uint8_t v___x_5698_; 
v___x_5698_ = 1;
if (v_only_5553_ == 0)
{
v___y_5586_ = v___y_5697_;
v___y_5587_ = v___x_5698_;
v_params_5588_ = v_params_5551_;
v___y_5589_ = v_a_5555_;
v___y_5590_ = v_a_5556_;
v___y_5591_ = v_a_5557_;
v___y_5592_ = v_a_5558_;
v___y_5593_ = v_a_5559_;
v___y_5594_ = v_a_5560_;
v___y_5595_ = v_a_5561_;
v___y_5596_ = v_a_5562_;
goto v___jp_5585_;
}
else
{
lean_object* v_config_5699_; lean_object* v_extensions_5700_; lean_object* v_extra_5701_; lean_object* v_extraInj_5702_; lean_object* v_extraFacts_5703_; lean_object* v_symPrios_5704_; lean_object* v_norm_5705_; lean_object* v_normProcs_5706_; lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5717_; 
v_config_5699_ = lean_ctor_get(v_params_5551_, 0);
v_extensions_5700_ = lean_ctor_get(v_params_5551_, 1);
v_extra_5701_ = lean_ctor_get(v_params_5551_, 2);
v_extraInj_5702_ = lean_ctor_get(v_params_5551_, 3);
v_extraFacts_5703_ = lean_ctor_get(v_params_5551_, 4);
v_symPrios_5704_ = lean_ctor_get(v_params_5551_, 5);
v_norm_5705_ = lean_ctor_get(v_params_5551_, 6);
v_normProcs_5706_ = lean_ctor_get(v_params_5551_, 7);
v_isSharedCheck_5717_ = !lean_is_exclusive(v_params_5551_);
if (v_isSharedCheck_5717_ == 0)
{
lean_object* v_unused_5718_; 
v_unused_5718_ = lean_ctor_get(v_params_5551_, 8);
lean_dec(v_unused_5718_);
v___x_5708_ = v_params_5551_;
v_isShared_5709_ = v_isSharedCheck_5717_;
goto v_resetjp_5707_;
}
else
{
lean_inc(v_normProcs_5706_);
lean_inc(v_norm_5705_);
lean_inc(v_symPrios_5704_);
lean_inc(v_extraFacts_5703_);
lean_inc(v_extraInj_5702_);
lean_inc(v_extra_5701_);
lean_inc(v_extensions_5700_);
lean_inc(v_config_5699_);
lean_dec(v_params_5551_);
v___x_5708_ = lean_box(0);
v_isShared_5709_ = v_isSharedCheck_5717_;
goto v_resetjp_5707_;
}
v_resetjp_5707_:
{
size_t v_sz_5710_; size_t v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v_params_5715_; 
v_sz_5710_ = lean_array_size(v_extensions_5700_);
v___x_5711_ = ((size_t)0ULL);
v___x_5712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_5710_, v___x_5711_, v_extensions_5700_);
v___x_5713_ = lean_box(0);
if (v_isShared_5709_ == 0)
{
lean_ctor_set(v___x_5708_, 8, v___x_5713_);
lean_ctor_set(v___x_5708_, 1, v___x_5712_);
v_params_5715_ = v___x_5708_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_config_5699_);
lean_ctor_set(v_reuseFailAlloc_5716_, 1, v___x_5712_);
lean_ctor_set(v_reuseFailAlloc_5716_, 2, v_extra_5701_);
lean_ctor_set(v_reuseFailAlloc_5716_, 3, v_extraInj_5702_);
lean_ctor_set(v_reuseFailAlloc_5716_, 4, v_extraFacts_5703_);
lean_ctor_set(v_reuseFailAlloc_5716_, 5, v_symPrios_5704_);
lean_ctor_set(v_reuseFailAlloc_5716_, 6, v_norm_5705_);
lean_ctor_set(v_reuseFailAlloc_5716_, 7, v_normProcs_5706_);
lean_ctor_set(v_reuseFailAlloc_5716_, 8, v___x_5713_);
v_params_5715_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
v___y_5586_ = v___y_5697_;
v___y_5587_ = v___x_5698_;
v_params_5588_ = v_params_5715_;
v___y_5589_ = v_a_5555_;
v___y_5590_ = v_a_5556_;
v___y_5591_ = v_a_5557_;
v___y_5592_ = v_a_5558_;
v___y_5593_ = v_a_5559_;
v___y_5594_ = v_a_5560_;
v___y_5595_ = v_a_5561_;
v___y_5596_ = v_a_5562_;
goto v___jp_5585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_5724_, lean_object* v_ps_5725_, lean_object* v_only_5726_, lean_object* v_k_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_){
_start:
{
uint8_t v_only_boxed_5737_; lean_object* v_res_5738_; 
v_only_boxed_5737_ = lean_unbox(v_only_5726_);
v_res_5738_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5724_, v_ps_5725_, v_only_boxed_5737_, v_k_5727_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_);
lean_dec(v_a_5735_);
lean_dec_ref(v_a_5734_);
lean_dec(v_a_5733_);
lean_dec_ref(v_a_5732_);
lean_dec(v_a_5731_);
lean_dec_ref(v_a_5730_);
lean_dec(v_a_5729_);
lean_dec_ref(v_a_5728_);
lean_dec_ref(v_ps_5725_);
return v_res_5738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_5739_, lean_object* v_params_5740_, lean_object* v_ps_5741_, uint8_t v_only_5742_, lean_object* v_k_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_){
_start:
{
lean_object* v___x_5753_; 
v___x_5753_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5740_, v_ps_5741_, v_only_5742_, v_k_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_);
return v___x_5753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_5754_, lean_object* v_params_5755_, lean_object* v_ps_5756_, lean_object* v_only_5757_, lean_object* v_k_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_){
_start:
{
uint8_t v_only_boxed_5768_; lean_object* v_res_5769_; 
v_only_boxed_5768_ = lean_unbox(v_only_5757_);
v_res_5769_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_5754_, v_params_5755_, v_ps_5756_, v_only_boxed_5768_, v_k_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_, v_a_5765_, v_a_5766_);
lean_dec(v_a_5766_);
lean_dec_ref(v_a_5765_);
lean_dec(v_a_5764_);
lean_dec_ref(v_a_5763_);
lean_dec(v_a_5762_);
lean_dec_ref(v_a_5761_);
lean_dec(v_a_5760_);
lean_dec_ref(v_a_5759_);
lean_dec_ref(v_ps_5756_);
return v_res_5769_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Param(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_Param(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_Param(builtin);
}
#ifdef __cplusplus
}
#endif
