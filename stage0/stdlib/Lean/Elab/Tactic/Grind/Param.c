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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Meta_Grind_CasesTypes_contains(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_checkDeprecatedCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SymbolPriorities_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "invalid `grind` parameter, only global declarations are allowed with this kind of modifier"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "`cases` parameter are not supported here"};
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
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid use of modifier in `grind` attribute `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "redundant parameter `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "`, `grind` uses local hypotheses automatically"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "invalid anchor, `only` modifier expected"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "invalid `-` occurrence, it can only used at the `grind` tactic entry point"};
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
lean_ctor_set(v___x_89_, 3, v___y_81_);
lean_ctor_set(v___x_89_, 4, v___y_80_);
lean_ctor_set(v___x_89_, 5, v___y_84_);
lean_ctor_set(v___x_89_, 6, v___y_83_);
lean_ctor_set(v___x_89_, 7, v___y_85_);
lean_ctor_set(v___x_89_, 8, v___y_86_);
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
v___y_80_ = v_extraFacts_95_;
v___y_81_ = v_extraInj_94_;
v___y_82_ = v_extra_93_;
v___y_83_ = v_norm_97_;
v___y_84_ = v_symPrios_96_;
v___y_85_ = v_normProcs_98_;
v___y_86_ = v_anchorRefs_x3f_99_;
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
v___y_80_ = v_extraFacts_95_;
v___y_81_ = v_extraInj_94_;
v___y_82_ = v_extra_93_;
v___y_83_ = v_norm_97_;
v___y_84_ = v_symPrios_96_;
v___y_85_ = v_normProcs_98_;
v___y_86_ = v_anchorRefs_x3f_99_;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object* v_params_306_, lean_object* v_as_307_, size_t v_i_308_, size_t v_stop_309_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = lean_usize_dec_eq(v_i_308_, v_stop_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; uint8_t v___x_312_; uint8_t v___x_313_; 
v___x_311_ = lean_array_uget_borrowed(v_as_307_, v_i_308_);
lean_inc(v___x_311_);
v___x_312_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_306_, v___x_311_);
v___x_313_ = lean_bool_not(v___x_312_);
if (v___x_313_ == 0)
{
size_t v___x_314_; size_t v___x_315_; 
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_add(v_i_308_, v___x_314_);
v_i_308_ = v___x_315_;
goto _start;
}
else
{
return v___x_313_;
}
}
else
{
uint8_t v___x_317_; 
v___x_317_ = 0;
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object* v_params_318_, lean_object* v_as_319_, lean_object* v_i_320_, lean_object* v_stop_321_){
_start:
{
size_t v_i_boxed_322_; size_t v_stop_boxed_323_; uint8_t v_res_324_; lean_object* v_r_325_; 
v_i_boxed_322_ = lean_unbox_usize(v_i_320_);
lean_dec(v_i_320_);
v_stop_boxed_323_ = lean_unbox_usize(v_stop_321_);
lean_dec(v_stop_321_);
v_res_324_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_318_, v_as_319_, v_i_boxed_322_, v_stop_boxed_323_);
lean_dec_ref(v_as_319_);
lean_dec_ref(v_params_318_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(lean_object* v_as_326_, size_t v_i_327_, size_t v_stop_328_, lean_object* v_b_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = lean_usize_dec_eq(v_i_327_, v_stop_328_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; size_t v___x_333_; size_t v___x_334_; 
v___x_331_ = lean_array_uget_borrowed(v_as_326_, v_i_327_);
lean_inc(v___x_331_);
v___x_332_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(v_b_329_, v___x_331_);
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_add(v_i_327_, v___x_333_);
v_i_327_ = v___x_334_;
v_b_329_ = v___x_332_;
goto _start;
}
else
{
return v_b_329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0___boxed(lean_object* v_as_336_, lean_object* v_i_337_, lean_object* v_stop_338_, lean_object* v_b_339_){
_start:
{
size_t v_i_boxed_340_; size_t v_stop_boxed_341_; lean_object* v_res_342_; 
v_i_boxed_340_ = lean_unbox_usize(v_i_337_);
lean_dec(v_i_337_);
v_stop_boxed_341_ = lean_unbox_usize(v_stop_338_);
lean_dec(v_stop_338_);
v_res_342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_as_336_, v_i_boxed_340_, v_stop_boxed_341_, v_b_339_);
lean_dec_ref(v_as_336_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(lean_object* v_params_343_, lean_object* v_declName_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v___x_353_; lean_object* v_env_354_; uint8_t v___x_355_; uint8_t v___x_356_; 
v___x_353_ = lean_st_ref_get(v_a_348_);
v_env_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc_ref(v_env_354_);
lean_dec(v___x_353_);
lean_inc(v_declName_344_);
v___x_355_ = l_Lean_wasOriginallyTheorem(v_env_354_, v_declName_344_);
v___x_356_ = lean_bool_not(v___x_355_);
if (v___x_356_ == 0)
{
uint8_t v___x_357_; 
lean_inc(v_declName_344_);
v___x_357_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_343_, v_declName_344_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_inc(v_declName_344_);
v___x_358_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_344_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_dec_ref_known(v___x_358_, 1);
goto v___jp_350_;
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_declName_344_);
lean_dec_ref(v_params_343_);
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
goto v___jp_350_;
}
}
else
{
lean_object* v___x_367_; 
lean_inc(v_declName_344_);
v___x_367_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_417_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_417_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_417_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_417_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
if (lean_obj_tag(v_a_368_) == 1)
{
lean_object* v_val_372_; uint8_t v___y_397_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v_val_372_ = lean_ctor_get(v_a_368_, 0);
lean_inc(v_val_372_);
lean_dec_ref_known(v_a_368_, 1);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_array_get_size(v_val_372_);
v___x_409_ = lean_nat_dec_lt(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = lean_bool_not(v___x_409_);
v___y_397_ = v___x_410_;
goto v___jp_396_;
}
else
{
if (v___x_409_ == 0)
{
uint8_t v___x_411_; 
v___x_411_ = lean_bool_not(v___x_409_);
v___y_397_ = v___x_411_;
goto v___jp_396_;
}
else
{
size_t v___x_412_; size_t v___x_413_; uint8_t v___x_414_; uint8_t v___x_415_; 
v___x_412_ = ((size_t)0ULL);
v___x_413_ = lean_usize_of_nat(v___x_408_);
v___x_414_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_343_, v_val_372_, v___x_412_, v___x_413_);
v___x_415_ = lean_bool_not(v___x_414_);
v___y_397_ = v___x_415_;
goto v___jp_396_;
}
}
v___jp_373_:
{
lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_array_get_size(v_val_372_);
v___x_376_ = lean_nat_dec_lt(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v_val_372_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v_params_343_);
v___x_378_ = v___x_370_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_params_343_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
else
{
uint8_t v___x_380_; 
v___x_380_ = lean_nat_dec_le(v___x_375_, v___x_375_);
if (v___x_380_ == 0)
{
if (v___x_376_ == 0)
{
lean_object* v___x_382_; 
lean_dec(v_val_372_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v_params_343_);
v___x_382_ = v___x_370_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_params_343_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_384_ = ((size_t)0ULL);
v___x_385_ = lean_usize_of_nat(v___x_375_);
v___x_386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_372_, v___x_384_, v___x_385_, v_params_343_);
lean_dec(v_val_372_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_386_);
v___x_388_ = v___x_370_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_390_ = ((size_t)0ULL);
v___x_391_ = lean_usize_of_nat(v___x_375_);
v___x_392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_372_, v___x_390_, v___x_391_, v_params_343_);
lean_dec(v_val_372_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_392_);
v___x_394_ = v___x_370_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
v___jp_396_:
{
if (v___y_397_ == 0)
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_344_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_dec_ref_known(v___x_398_, 1);
goto v___jp_373_;
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_val_372_);
lean_del_object(v___x_370_);
lean_dec_ref(v_params_343_);
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_dec(v_declName_344_);
goto v___jp_373_;
}
}
}
else
{
lean_object* v___x_416_; 
lean_del_object(v___x_370_);
lean_dec(v_a_368_);
lean_dec_ref(v_params_343_);
v___x_416_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_344_, v_a_347_, v_a_348_);
return v___x_416_;
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec(v_declName_344_);
lean_dec_ref(v_params_343_);
v_a_418_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_367_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_367_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
v___jp_350_:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(v_params_343_, v_declName_344_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch___boxed(lean_object* v_params_426_, lean_object* v_declName_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_params_426_, v_declName_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(lean_object* v_params_434_, lean_object* v_declName_435_){
_start:
{
lean_object* v_config_436_; lean_object* v_extensions_437_; lean_object* v_extra_438_; lean_object* v_extraInj_439_; lean_object* v_extraFacts_440_; lean_object* v_symPrios_441_; lean_object* v_norm_442_; lean_object* v_normProcs_443_; lean_object* v_anchorRefs_x3f_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_config_436_ = lean_ctor_get(v_params_434_, 0);
v_extensions_437_ = lean_ctor_get(v_params_434_, 1);
v_extra_438_ = lean_ctor_get(v_params_434_, 2);
v_extraInj_439_ = lean_ctor_get(v_params_434_, 3);
v_extraFacts_440_ = lean_ctor_get(v_params_434_, 4);
v_symPrios_441_ = lean_ctor_get(v_params_434_, 5);
v_norm_442_ = lean_ctor_get(v_params_434_, 6);
v_normProcs_443_ = lean_ctor_get(v_params_434_, 7);
v_anchorRefs_x3f_444_ = lean_ctor_get(v_params_434_, 8);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_array_get_size(v_extensions_437_);
v___x_447_ = lean_nat_dec_lt(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_dec(v_declName_435_);
return v_params_434_;
}
else
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_472_; 
lean_inc(v_anchorRefs_x3f_444_);
lean_inc_ref(v_normProcs_443_);
lean_inc_ref(v_norm_442_);
lean_inc_ref(v_symPrios_441_);
lean_inc_ref(v_extraFacts_440_);
lean_inc_ref(v_extraInj_439_);
lean_inc_ref(v_extra_438_);
lean_inc_ref(v_extensions_437_);
lean_inc_ref(v_config_436_);
v_isSharedCheck_472_ = !lean_is_exclusive(v_params_434_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; lean_object* v_unused_479_; lean_object* v_unused_480_; lean_object* v_unused_481_; 
v_unused_473_ = lean_ctor_get(v_params_434_, 8);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_params_434_, 7);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_params_434_, 6);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_params_434_, 5);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_params_434_, 4);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_params_434_, 3);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_params_434_, 2);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_params_434_, 1);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_params_434_, 0);
lean_dec(v_unused_481_);
v___x_449_ = v_params_434_;
v_isShared_450_ = v_isSharedCheck_472_;
goto v_resetjp_448_;
}
else
{
lean_dec(v_params_434_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_472_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_v_451_; lean_object* v_casesTypes_452_; lean_object* v_extThms_453_; lean_object* v_funCC_454_; lean_object* v_ematch_455_; lean_object* v_inj_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_471_; 
v_v_451_ = lean_array_fget(v_extensions_437_, v___x_445_);
v_casesTypes_452_ = lean_ctor_get(v_v_451_, 0);
v_extThms_453_ = lean_ctor_get(v_v_451_, 1);
v_funCC_454_ = lean_ctor_get(v_v_451_, 2);
v_ematch_455_ = lean_ctor_get(v_v_451_, 3);
v_inj_456_ = lean_ctor_get(v_v_451_, 4);
v_isSharedCheck_471_ = !lean_is_exclusive(v_v_451_);
if (v_isSharedCheck_471_ == 0)
{
v___x_458_ = v_v_451_;
v_isShared_459_ = v_isSharedCheck_471_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_inj_456_);
lean_inc(v_ematch_455_);
lean_inc(v_funCC_454_);
lean_inc(v_extThms_453_);
lean_inc(v_casesTypes_452_);
lean_dec(v_v_451_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_471_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v_xs_x27_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_460_ = lean_box(0);
v_xs_x27_461_ = lean_array_fset(v_extensions_437_, v___x_445_, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v_declName_435_);
v___x_463_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_inj_456_, v___x_462_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v___x_463_);
v___x_465_ = v___x_458_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_casesTypes_452_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_extThms_453_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_funCC_454_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_ematch_455_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v___x_463_);
v___x_465_ = v_reuseFailAlloc_470_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = lean_array_fset(v_xs_x27_461_, v___x_445_, v___x_465_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v___x_466_);
v___x_468_ = v___x_449_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_config_436_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_extra_438_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_extraInj_439_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v_extraFacts_440_);
lean_ctor_set(v_reuseFailAlloc_469_, 5, v_symPrios_441_);
lean_ctor_set(v_reuseFailAlloc_469_, 6, v_norm_442_);
lean_ctor_set(v_reuseFailAlloc_469_, 7, v_normProcs_443_);
lean_ctor_set(v_reuseFailAlloc_469_, 8, v_anchorRefs_x3f_444_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(lean_object* v_origin_482_, lean_object* v_as_483_, size_t v_sz_484_, size_t v_i_485_, lean_object* v_b_486_){
_start:
{
lean_object* v_a_488_; uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_lt(v_i_485_, v_sz_484_);
if (v___x_492_ == 0)
{
return v_b_486_;
}
else
{
lean_object* v_a_493_; lean_object* v_ematch_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_a_493_ = lean_array_uget_borrowed(v_as_483_, v_i_485_);
v_ematch_494_ = lean_ctor_get(v_a_493_, 3);
v___x_495_ = l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(v_ematch_494_, v_origin_482_);
v___x_496_ = l_List_isEmpty___redArg(v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
v___x_497_ = l_List_appendTR___redArg(v_b_486_, v___x_495_);
v_a_488_ = v___x_497_;
goto v___jp_487_;
}
else
{
lean_dec(v___x_495_);
v_a_488_ = v_b_486_;
goto v___jp_487_;
}
}
v___jp_487_:
{
size_t v___x_489_; size_t v___x_490_; 
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_485_, v___x_489_);
v_i_485_ = v___x_490_;
v_b_486_ = v_a_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0___boxed(lean_object* v_origin_498_, lean_object* v_as_499_, lean_object* v_sz_500_, lean_object* v_i_501_, lean_object* v_b_502_){
_start:
{
size_t v_sz_boxed_503_; size_t v_i_boxed_504_; lean_object* v_res_505_; 
v_sz_boxed_503_ = lean_unbox_usize(v_sz_500_);
lean_dec(v_sz_500_);
v_i_boxed_504_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_498_, v_as_499_, v_sz_boxed_503_, v_i_boxed_504_, v_b_502_);
lean_dec_ref(v_as_499_);
lean_dec_ref(v_origin_498_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(lean_object* v_s_506_, lean_object* v_origin_507_){
_start:
{
lean_object* v_result_508_; size_t v_sz_509_; size_t v___x_510_; lean_object* v___x_511_; 
v_result_508_ = lean_box(0);
v_sz_509_ = lean_array_size(v_s_506_);
v___x_510_ = ((size_t)0ULL);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_507_, v_s_506_, v_sz_509_, v___x_510_, v_result_508_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor___boxed(lean_object* v_s_512_, lean_object* v_origin_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_512_, v_origin_513_);
lean_dec_ref(v_origin_513_);
lean_dec_ref(v_s_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(lean_object* v_upperBound_515_, lean_object* v_s_516_, lean_object* v_origin_517_, lean_object* v_a_518_, lean_object* v_b_519_){
_start:
{
lean_object* v_a_521_; uint8_t v___x_525_; 
v___x_525_ = lean_nat_dec_lt(v_a_518_, v_upperBound_515_);
if (v___x_525_ == 0)
{
lean_dec(v_a_518_);
return v_b_519_;
}
else
{
lean_object* v___x_526_; lean_object* v_ematch_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_526_ = lean_array_fget_borrowed(v_s_516_, v_a_518_);
v_ematch_527_ = lean_ctor_get(v___x_526_, 3);
v___x_528_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_ematch_527_, v_origin_517_);
v___x_529_ = l_List_isEmpty___redArg(v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
v___x_530_ = l_List_appendTR___redArg(v_b_519_, v___x_528_);
v_a_521_ = v___x_530_;
goto v___jp_520_;
}
else
{
lean_dec(v___x_528_);
v_a_521_ = v_b_519_;
goto v___jp_520_;
}
}
v___jp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_a_518_, v___x_522_);
lean_dec(v_a_518_);
v_a_518_ = v___x_523_;
v_b_519_ = v_a_521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg___boxed(lean_object* v_upperBound_531_, lean_object* v_s_532_, lean_object* v_origin_533_, lean_object* v_a_534_, lean_object* v_b_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_531_, v_s_532_, v_origin_533_, v_a_534_, v_b_535_);
lean_dec_ref(v_origin_533_);
lean_dec_ref(v_s_532_);
lean_dec(v_upperBound_531_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find(lean_object* v_s_537_, lean_object* v_origin_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_r_541_; lean_object* v___x_542_; 
v___x_539_ = lean_array_get_size(v_s_537_);
v___x_540_ = lean_unsigned_to_nat(0u);
v_r_541_ = lean_box(0);
v___x_542_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v___x_539_, v_s_537_, v_origin_538_, v___x_540_, v_r_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find___boxed(lean_object* v_s_543_, lean_object* v_origin_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Meta_Grind_ExtensionStateArray_find(v_s_543_, v_origin_544_);
lean_dec_ref(v_origin_544_);
lean_dec_ref(v_s_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(lean_object* v_upperBound_546_, lean_object* v_s_547_, lean_object* v_origin_548_, lean_object* v_inst_549_, lean_object* v_R_550_, lean_object* v_a_551_, lean_object* v_b_552_, lean_object* v_c_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_546_, v_s_547_, v_origin_548_, v_a_551_, v_b_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___boxed(lean_object* v_upperBound_555_, lean_object* v_s_556_, lean_object* v_origin_557_, lean_object* v_inst_558_, lean_object* v_R_559_, lean_object* v_a_560_, lean_object* v_b_561_, lean_object* v_c_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(v_upperBound_555_, v_s_556_, v_origin_557_, v_inst_558_, v_R_559_, v_a_560_, v_b_561_, v_c_562_);
lean_dec_ref(v_origin_557_);
lean_dec_ref(v_s_556_);
lean_dec(v_upperBound_555_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(lean_object* v_msgData_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; lean_object* v_env_571_; lean_object* v___x_572_; lean_object* v_mctx_573_; lean_object* v_lctx_574_; lean_object* v_options_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_570_ = lean_st_ref_get(v___y_568_);
v_env_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_env_571_);
lean_dec(v___x_570_);
v___x_572_ = lean_st_ref_get(v___y_566_);
v_mctx_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc_ref(v_mctx_573_);
lean_dec(v___x_572_);
v_lctx_574_ = lean_ctor_get(v___y_565_, 2);
v_options_575_ = lean_ctor_get(v___y_567_, 2);
lean_inc_ref(v_options_575_);
lean_inc_ref(v_lctx_574_);
v___x_576_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_576_, 0, v_env_571_);
lean_ctor_set(v___x_576_, 1, v_mctx_573_);
lean_ctor_set(v___x_576_, 2, v_lctx_574_);
lean_ctor_set(v___x_576_, 3, v_options_575_);
v___x_577_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_msgData_564_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msgData_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_585_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_586_, lean_object* v_opt_587_){
_start:
{
lean_object* v_name_588_; lean_object* v_defValue_589_; lean_object* v_map_590_; lean_object* v___x_591_; 
v_name_588_ = lean_ctor_get(v_opt_587_, 0);
v_defValue_589_ = lean_ctor_get(v_opt_587_, 1);
v_map_590_ = lean_ctor_get(v_opts_586_, 0);
v___x_591_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_590_, v_name_588_);
if (lean_obj_tag(v___x_591_) == 0)
{
uint8_t v___x_592_; 
v___x_592_ = lean_unbox(v_defValue_589_);
return v___x_592_;
}
else
{
lean_object* v_val_593_; 
v_val_593_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_val_593_);
lean_dec_ref_known(v___x_591_, 1);
if (lean_obj_tag(v_val_593_) == 1)
{
uint8_t v_v_594_; 
v_v_594_ = lean_ctor_get_uint8(v_val_593_, 0);
lean_dec_ref_known(v_val_593_, 0);
return v_v_594_;
}
else
{
uint8_t v___x_595_; 
lean_dec(v_val_593_);
v___x_595_ = lean_unbox(v_defValue_589_);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_596_, lean_object* v_opt_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_opts_596_, v_opt_597_);
lean_dec_ref(v_opt_597_);
lean_dec_ref(v_opts_596_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_608_, uint8_t v_suppressElabErrors_609_, lean_object* v_x_610_){
_start:
{
if (lean_obj_tag(v_x_610_) == 1)
{
lean_object* v_pre_611_; 
v_pre_611_ = lean_ctor_get(v_x_610_, 0);
switch(lean_obj_tag(v_pre_611_))
{
case 1:
{
lean_object* v_pre_612_; 
v_pre_612_ = lean_ctor_get(v_pre_611_, 0);
switch(lean_obj_tag(v_pre_612_))
{
case 0:
{
lean_object* v_str_613_; lean_object* v_str_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_str_613_ = lean_ctor_get(v_x_610_, 1);
v_str_614_ = lean_ctor_get(v_pre_611_, 1);
v___x_615_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_616_ = lean_string_dec_eq(v_str_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_618_ = lean_string_dec_eq(v_str_614_, v___x_617_);
if (v___x_618_ == 0)
{
return v___y_608_;
}
else
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_620_ = lean_string_dec_eq(v_str_613_, v___x_619_);
if (v___x_620_ == 0)
{
return v___y_608_;
}
else
{
return v_suppressElabErrors_609_;
}
}
}
else
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_622_ = lean_string_dec_eq(v_str_613_, v___x_621_);
if (v___x_622_ == 0)
{
return v___y_608_;
}
else
{
return v_suppressElabErrors_609_;
}
}
}
case 1:
{
lean_object* v_pre_623_; 
v_pre_623_ = lean_ctor_get(v_pre_612_, 0);
if (lean_obj_tag(v_pre_623_) == 0)
{
lean_object* v_str_624_; lean_object* v_str_625_; lean_object* v_str_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_str_624_ = lean_ctor_get(v_x_610_, 1);
v_str_625_ = lean_ctor_get(v_pre_611_, 1);
v_str_626_ = lean_ctor_get(v_pre_612_, 1);
v___x_627_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_628_ = lean_string_dec_eq(v_str_626_, v___x_627_);
if (v___x_628_ == 0)
{
return v___y_608_;
}
else
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_630_ = lean_string_dec_eq(v_str_625_, v___x_629_);
if (v___x_630_ == 0)
{
return v___y_608_;
}
else
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_632_ = lean_string_dec_eq(v_str_624_, v___x_631_);
if (v___x_632_ == 0)
{
return v___y_608_;
}
else
{
return v_suppressElabErrors_609_;
}
}
}
}
else
{
return v___y_608_;
}
}
default: 
{
return v___y_608_;
}
}
}
case 0:
{
lean_object* v_str_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_str_633_ = lean_ctor_get(v_x_610_, 1);
v___x_634_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_635_ = lean_string_dec_eq(v_str_633_, v___x_634_);
if (v___x_635_ == 0)
{
return v___y_608_;
}
else
{
return v_suppressElabErrors_609_;
}
}
default: 
{
return v___y_608_;
}
}
}
else
{
return v___y_608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_636_, lean_object* v_suppressElabErrors_637_, lean_object* v_x_638_){
_start:
{
uint8_t v___y_4233__boxed_639_; uint8_t v_suppressElabErrors_boxed_640_; uint8_t v_res_641_; lean_object* v_r_642_; 
v___y_4233__boxed_639_ = lean_unbox(v___y_636_);
v_suppressElabErrors_boxed_640_ = lean_unbox(v_suppressElabErrors_637_);
v_res_641_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v___y_4233__boxed_639_, v_suppressElabErrors_boxed_640_, v_x_638_);
lean_dec(v_x_638_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_644_, lean_object* v_msgData_645_, uint8_t v_severity_646_, uint8_t v_isSilent_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
uint8_t v___y_654_; lean_object* v___y_655_; uint8_t v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_690_; lean_object* v___y_691_; uint8_t v___y_692_; uint8_t v___y_693_; lean_object* v___y_694_; uint8_t v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; uint8_t v___y_718_; uint8_t v___y_719_; uint8_t v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; uint8_t v___y_729_; uint8_t v___y_730_; lean_object* v___y_731_; uint8_t v___y_732_; uint8_t v___x_737_; lean_object* v___y_739_; lean_object* v___y_740_; uint8_t v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; uint8_t v___y_744_; uint8_t v___y_745_; uint8_t v___y_747_; uint8_t v___x_762_; 
v___x_737_ = 2;
v___x_762_ = l_Lean_instBEqMessageSeverity_beq(v_severity_646_, v___x_737_);
if (v___x_762_ == 0)
{
v___y_747_ = v___x_762_;
goto v___jp_746_;
}
else
{
uint8_t v___x_763_; 
lean_inc_ref(v_msgData_645_);
v___x_763_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_645_);
v___y_747_ = v___x_763_;
goto v___jp_746_;
}
v___jp_653_:
{
lean_object* v___x_663_; lean_object* v_currNamespace_664_; lean_object* v_openDecls_665_; lean_object* v_env_666_; lean_object* v_nextMacroScope_667_; lean_object* v_ngen_668_; lean_object* v_auxDeclNGen_669_; lean_object* v_traceState_670_; lean_object* v_cache_671_; lean_object* v_messages_672_; lean_object* v_infoState_673_; lean_object* v_snapshotTasks_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_688_; 
v___x_663_ = lean_st_ref_take(v___y_662_);
v_currNamespace_664_ = lean_ctor_get(v___y_661_, 6);
v_openDecls_665_ = lean_ctor_get(v___y_661_, 7);
v_env_666_ = lean_ctor_get(v___x_663_, 0);
v_nextMacroScope_667_ = lean_ctor_get(v___x_663_, 1);
v_ngen_668_ = lean_ctor_get(v___x_663_, 2);
v_auxDeclNGen_669_ = lean_ctor_get(v___x_663_, 3);
v_traceState_670_ = lean_ctor_get(v___x_663_, 4);
v_cache_671_ = lean_ctor_get(v___x_663_, 5);
v_messages_672_ = lean_ctor_get(v___x_663_, 6);
v_infoState_673_ = lean_ctor_get(v___x_663_, 7);
v_snapshotTasks_674_ = lean_ctor_get(v___x_663_, 8);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_688_ == 0)
{
v___x_676_ = v___x_663_;
v_isShared_677_ = v_isSharedCheck_688_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_snapshotTasks_674_);
lean_inc(v_infoState_673_);
lean_inc(v_messages_672_);
lean_inc(v_cache_671_);
lean_inc(v_traceState_670_);
lean_inc(v_auxDeclNGen_669_);
lean_inc(v_ngen_668_);
lean_inc(v_nextMacroScope_667_);
lean_inc(v_env_666_);
lean_dec(v___x_663_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_688_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
lean_inc(v_openDecls_665_);
lean_inc(v_currNamespace_664_);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v_currNamespace_664_);
lean_ctor_set(v___x_678_, 1, v_openDecls_665_);
v___x_679_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___y_658_);
lean_inc_ref(v___y_657_);
lean_inc_ref(v___y_660_);
v___x_680_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_680_, 0, v___y_660_);
lean_ctor_set(v___x_680_, 1, v___y_655_);
lean_ctor_set(v___x_680_, 2, v___y_659_);
lean_ctor_set(v___x_680_, 3, v___y_657_);
lean_ctor_set(v___x_680_, 4, v___x_679_);
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*5, v___y_656_);
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*5 + 1, v___y_654_);
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*5 + 2, v_isSilent_647_);
v___x_681_ = l_Lean_MessageLog_add(v___x_680_, v_messages_672_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 6, v___x_681_);
v___x_683_ = v___x_676_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_env_666_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_nextMacroScope_667_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_ngen_668_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_auxDeclNGen_669_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_traceState_670_);
lean_ctor_set(v_reuseFailAlloc_687_, 5, v_cache_671_);
lean_ctor_set(v_reuseFailAlloc_687_, 6, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_687_, 7, v_infoState_673_);
lean_ctor_set(v_reuseFailAlloc_687_, 8, v_snapshotTasks_674_);
v___x_683_ = v_reuseFailAlloc_687_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_st_ref_set(v___y_662_, v___x_683_);
v___x_685_ = lean_box(0);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
}
v___jp_689_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_713_; 
v___x_698_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_645_);
v___x_699_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_698_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_713_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_713_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_713_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_inc_ref_n(v___y_691_, 2);
v___x_704_ = l_Lean_FileMap_toPosition(v___y_691_, v___y_694_);
lean_dec(v___y_694_);
v___x_705_ = l_Lean_FileMap_toPosition(v___y_691_, v___y_697_);
lean_dec(v___y_697_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
v___x_707_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_692_ == 0)
{
lean_del_object(v___x_702_);
lean_dec_ref(v___y_690_);
v___y_654_ = v___y_693_;
v___y_655_ = v___x_704_;
v___y_656_ = v___y_695_;
v___y_657_ = v___x_707_;
v___y_658_ = v_a_700_;
v___y_659_ = v___x_706_;
v___y_660_ = v___y_696_;
v___y_661_ = v___y_650_;
v___y_662_ = v___y_651_;
goto v___jp_653_;
}
else
{
uint8_t v___x_708_; 
lean_inc(v_a_700_);
v___x_708_ = l_Lean_MessageData_hasTag(v___y_690_, v_a_700_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_711_; 
lean_dec_ref_known(v___x_706_, 1);
lean_dec_ref(v___x_704_);
lean_dec(v_a_700_);
v___x_709_ = lean_box(0);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_709_);
v___x_711_ = v___x_702_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
else
{
lean_del_object(v___x_702_);
v___y_654_ = v___y_693_;
v___y_655_ = v___x_704_;
v___y_656_ = v___y_695_;
v___y_657_ = v___x_707_;
v___y_658_ = v_a_700_;
v___y_659_ = v___x_706_;
v___y_660_ = v___y_696_;
v___y_661_ = v___y_650_;
v___y_662_ = v___y_651_;
goto v___jp_653_;
}
}
}
}
v___jp_714_:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_Syntax_getTailPos_x3f(v___y_716_, v___y_720_);
lean_dec(v___y_716_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_inc(v___y_722_);
v___y_690_ = v___y_715_;
v___y_691_ = v___y_717_;
v___y_692_ = v___y_718_;
v___y_693_ = v___y_719_;
v___y_694_ = v___y_722_;
v___y_695_ = v___y_720_;
v___y_696_ = v___y_721_;
v___y_697_ = v___y_722_;
goto v___jp_689_;
}
else
{
lean_object* v_val_724_; 
v_val_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_val_724_);
lean_dec_ref_known(v___x_723_, 1);
v___y_690_ = v___y_715_;
v___y_691_ = v___y_717_;
v___y_692_ = v___y_718_;
v___y_693_ = v___y_719_;
v___y_694_ = v___y_722_;
v___y_695_ = v___y_720_;
v___y_696_ = v___y_721_;
v___y_697_ = v_val_724_;
goto v___jp_689_;
}
}
v___jp_725_:
{
lean_object* v_ref_733_; lean_object* v___x_734_; 
v_ref_733_ = l_Lean_replaceRef(v_ref_644_, v___y_727_);
v___x_734_ = l_Lean_Syntax_getPos_x3f(v_ref_733_, v___y_730_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v___x_735_; 
v___x_735_ = lean_unsigned_to_nat(0u);
v___y_715_ = v___y_726_;
v___y_716_ = v_ref_733_;
v___y_717_ = v___y_728_;
v___y_718_ = v___y_729_;
v___y_719_ = v___y_732_;
v___y_720_ = v___y_730_;
v___y_721_ = v___y_731_;
v___y_722_ = v___x_735_;
goto v___jp_714_;
}
else
{
lean_object* v_val_736_; 
v_val_736_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_val_736_);
lean_dec_ref_known(v___x_734_, 1);
v___y_715_ = v___y_726_;
v___y_716_ = v_ref_733_;
v___y_717_ = v___y_728_;
v___y_718_ = v___y_729_;
v___y_719_ = v___y_732_;
v___y_720_ = v___y_730_;
v___y_721_ = v___y_731_;
v___y_722_ = v_val_736_;
goto v___jp_714_;
}
}
v___jp_738_:
{
if (v___y_745_ == 0)
{
v___y_726_ = v___y_742_;
v___y_727_ = v___y_739_;
v___y_728_ = v___y_740_;
v___y_729_ = v___y_741_;
v___y_730_ = v___y_744_;
v___y_731_ = v___y_743_;
v___y_732_ = v_severity_646_;
goto v___jp_725_;
}
else
{
v___y_726_ = v___y_742_;
v___y_727_ = v___y_739_;
v___y_728_ = v___y_740_;
v___y_729_ = v___y_741_;
v___y_730_ = v___y_744_;
v___y_731_ = v___y_743_;
v___y_732_ = v___x_737_;
goto v___jp_725_;
}
}
v___jp_746_:
{
if (v___y_747_ == 0)
{
lean_object* v_fileName_748_; lean_object* v_fileMap_749_; lean_object* v_options_750_; lean_object* v_ref_751_; uint8_t v_suppressElabErrors_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___f_755_; uint8_t v___x_756_; uint8_t v___x_757_; 
v_fileName_748_ = lean_ctor_get(v___y_650_, 0);
v_fileMap_749_ = lean_ctor_get(v___y_650_, 1);
v_options_750_ = lean_ctor_get(v___y_650_, 2);
v_ref_751_ = lean_ctor_get(v___y_650_, 5);
v_suppressElabErrors_752_ = lean_ctor_get_uint8(v___y_650_, sizeof(void*)*14 + 1);
v___x_753_ = lean_box(v___y_747_);
v___x_754_ = lean_box(v_suppressElabErrors_752_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_755_, 0, v___x_753_);
lean_closure_set(v___f_755_, 1, v___x_754_);
v___x_756_ = 1;
v___x_757_ = l_Lean_instBEqMessageSeverity_beq(v_severity_646_, v___x_756_);
if (v___x_757_ == 0)
{
v___y_739_ = v_ref_751_;
v___y_740_ = v_fileMap_749_;
v___y_741_ = v_suppressElabErrors_752_;
v___y_742_ = v___f_755_;
v___y_743_ = v_fileName_748_;
v___y_744_ = v___y_747_;
v___y_745_ = v___x_757_;
goto v___jp_738_;
}
else
{
lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_758_ = l_Lean_warningAsError;
v___x_759_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_750_, v___x_758_);
v___y_739_ = v_ref_751_;
v___y_740_ = v_fileMap_749_;
v___y_741_ = v_suppressElabErrors_752_;
v___y_742_ = v___f_755_;
v___y_743_ = v_fileName_748_;
v___y_744_ = v___y_747_;
v___y_745_ = v___x_759_;
goto v___jp_738_;
}
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec_ref(v_msgData_645_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_764_, lean_object* v_msgData_765_, lean_object* v_severity_766_, lean_object* v_isSilent_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
uint8_t v_severity_boxed_773_; uint8_t v_isSilent_boxed_774_; lean_object* v_res_775_; 
v_severity_boxed_773_ = lean_unbox(v_severity_766_);
v_isSilent_boxed_774_ = lean_unbox(v_isSilent_767_);
v_res_775_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_764_, v_msgData_765_, v_severity_boxed_773_, v_isSilent_boxed_774_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v_ref_764_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* v_msgData_776_, uint8_t v_severity_777_, uint8_t v_isSilent_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_ref_784_; lean_object* v___x_785_; 
v_ref_784_ = lean_ctor_get(v___y_781_, 5);
v___x_785_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_784_, v_msgData_776_, v_severity_777_, v_isSilent_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* v_msgData_786_, lean_object* v_severity_787_, lean_object* v_isSilent_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v_severity_boxed_794_; uint8_t v_isSilent_boxed_795_; lean_object* v_res_796_; 
v_severity_boxed_794_ = lean_unbox(v_severity_787_);
v_isSilent_boxed_795_ = lean_unbox(v_isSilent_788_);
v_res_796_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_786_, v_severity_boxed_794_, v_isSilent_boxed_795_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* v_msgData_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
uint8_t v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; 
v___x_803_ = 1;
v___x_804_ = 0;
v___x_805_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_797_, v___x_803_, v___x_804_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* v_msgData_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
return v_res_812_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
if (lean_obj_tag(v_a_816_) == 0)
{
lean_object* v___x_818_; 
v___x_818_ = l_List_reverse___redArg(v_a_817_);
return v___x_818_;
}
else
{
lean_object* v_head_819_; lean_object* v_tail_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_833_; 
v_head_819_ = lean_ctor_get(v_a_816_, 0);
v_tail_820_ = lean_ctor_get(v_a_816_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_a_816_);
if (v_isSharedCheck_833_ == 0)
{
v___x_822_ = v_a_816_;
v_isShared_823_ = v_isSharedCheck_833_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_tail_820_);
lean_inc(v_head_819_);
lean_dec(v_a_816_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_833_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v_minIndexable_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v_minIndexable_824_ = 0;
v___x_825_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_826_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_819_, v_minIndexable_824_);
lean_dec(v_head_819_);
v___x_827_ = l_Lean_stringToMessageData(v___x_826_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_825_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_a_817_);
lean_ctor_set(v___x_822_, 0, v___x_828_);
v___x_830_ = v___x_822_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_a_817_);
v___x_830_ = v_reuseFailAlloc_832_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
v_a_816_ = v_tail_820_;
v_a_817_ = v___x_830_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
if (lean_obj_tag(v_a_834_) == 0)
{
lean_object* v___x_836_; 
v___x_836_ = l_List_reverse___redArg(v_a_835_);
return v___x_836_;
}
else
{
lean_object* v_head_837_; lean_object* v_tail_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_846_; 
v_head_837_ = lean_ctor_get(v_a_834_, 0);
v_tail_838_ = lean_ctor_get(v_a_834_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v_a_834_);
if (v_isSharedCheck_846_ == 0)
{
v___x_840_ = v_a_834_;
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_tail_838_);
lean_inc(v_head_837_);
lean_dec(v_a_834_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v_a_835_);
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_head_837_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_a_835_);
v___x_843_ = v_reuseFailAlloc_845_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
v_a_834_ = v_tail_838_;
v_a_835_ = v___x_843_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
v___x_849_ = l_Lean_stringToMessageData(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* v_s_856_, lean_object* v_declName_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_kinds_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v_ks_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_inc(v_declName_857_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v_declName_857_);
v___x_889_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_856_, v___x_888_);
lean_dec_ref_known(v___x_888_, 1);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v_declName_857_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
else
{
lean_object* v_head_892_; lean_object* v_tail_893_; uint8_t v_minIndexable_894_; uint8_t v_gen_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; 
v_head_892_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_head_892_);
v_tail_893_ = lean_ctor_get(v___x_889_, 1);
lean_inc(v_tail_893_);
v_minIndexable_894_ = 0;
if (lean_obj_tag(v_tail_893_) == 0)
{
lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_915_; 
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; lean_object* v_unused_917_; 
v_unused_916_ = lean_ctor_get(v___x_889_, 1);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v___x_889_, 0);
lean_dec(v_unused_917_);
v___x_907_ = v___x_889_;
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
else
{
lean_dec(v___x_889_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_909_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_910_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_892_, v_minIndexable_894_);
lean_dec(v_head_892_);
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 7);
lean_ctor_set(v___x_907_, 1, v___x_911_);
lean_ctor_set(v___x_907_, 0, v___x_909_);
v___x_913_ = v___x_907_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
v_kinds_864_ = v___x_913_;
v___y_865_ = v_a_858_;
v___y_866_ = v_a_859_;
v___y_867_ = v_a_860_;
v___y_868_ = v_a_861_;
goto v___jp_863_;
}
}
}
else
{
lean_object* v_head_918_; 
v_head_918_ = lean_ctor_get(v_tail_893_, 0);
switch(lean_obj_tag(v_head_918_))
{
case 1:
{
lean_object* v_tail_919_; 
v_tail_919_ = lean_ctor_get(v_tail_893_, 1);
lean_inc(v_tail_919_);
lean_dec_ref_known(v_tail_893_, 2);
if (lean_obj_tag(v_tail_919_) == 0)
{
if (lean_obj_tag(v_head_892_) == 0)
{
uint8_t v_gen_920_; 
lean_dec_ref_known(v___x_889_, 2);
v_gen_920_ = lean_ctor_get_uint8(v_head_892_, 0);
lean_dec_ref_known(v_head_892_, 0);
v_gen_896_ = v_gen_920_;
v___y_897_ = v_a_858_;
v___y_898_ = v_a_859_;
v___y_899_ = v_a_860_;
v___y_900_ = v_a_861_;
goto v___jp_895_;
}
else
{
lean_dec(v_head_892_);
v_ks_879_ = v___x_889_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
v___y_882_ = v_a_860_;
v___y_883_ = v_a_861_;
goto v___jp_878_;
}
}
else
{
lean_dec(v_tail_919_);
lean_dec(v_head_892_);
v_ks_879_ = v___x_889_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
v___y_882_ = v_a_860_;
v___y_883_ = v_a_861_;
goto v___jp_878_;
}
}
case 0:
{
lean_object* v_tail_921_; 
v_tail_921_ = lean_ctor_get(v_tail_893_, 1);
lean_inc(v_tail_921_);
lean_dec_ref_known(v_tail_893_, 2);
if (lean_obj_tag(v_tail_921_) == 0)
{
if (lean_obj_tag(v_head_892_) == 1)
{
uint8_t v_gen_922_; 
lean_dec_ref_known(v___x_889_, 2);
v_gen_922_ = lean_ctor_get_uint8(v_head_892_, 0);
lean_dec_ref_known(v_head_892_, 0);
v_gen_896_ = v_gen_922_;
v___y_897_ = v_a_858_;
v___y_898_ = v_a_859_;
v___y_899_ = v_a_860_;
v___y_900_ = v_a_861_;
goto v___jp_895_;
}
else
{
lean_dec(v_head_892_);
v_ks_879_ = v___x_889_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
v___y_882_ = v_a_860_;
v___y_883_ = v_a_861_;
goto v___jp_878_;
}
}
else
{
lean_dec(v_tail_921_);
lean_dec(v_head_892_);
v_ks_879_ = v___x_889_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
v___y_882_ = v_a_860_;
v___y_883_ = v_a_861_;
goto v___jp_878_;
}
}
default: 
{
lean_dec_ref_known(v_tail_893_, 2);
lean_dec(v_head_892_);
v_ks_879_ = v___x_889_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
v___y_882_ = v_a_860_;
v___y_883_ = v_a_861_;
goto v___jp_878_;
}
}
}
v___jp_895_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_901_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_902_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_902_, 0, v_gen_896_);
v___x_903_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v___x_902_, v_minIndexable_894_);
lean_dec_ref_known(v___x_902_, 0);
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_901_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v_kinds_864_ = v___x_905_;
v___y_865_ = v___y_897_;
v___y_866_ = v___y_898_;
v___y_867_ = v___y_899_;
v___y_868_ = v___y_900_;
goto v___jp_863_;
}
}
v___jp_863_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_869_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
v___x_870_ = l_Lean_MessageData_ofName(v_declName_857_);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v_kinds_864_);
v___x_875_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v___x_876_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_877_;
}
v___jp_878_:
{
lean_object* v___x_884_; lean_object* v_ks_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_884_ = lean_box(0);
v_ks_885_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(v_ks_879_, v___x_884_);
v___x_886_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(v_ks_885_, v___x_884_);
v___x_887_ = l_Lean_MessageData_ofList(v___x_886_);
v_kinds_864_ = v___x_887_;
v___y_865_ = v___y_880_;
v___y_866_ = v___y_881_;
v___y_867_ = v___y_882_;
v___y_868_ = v___y_883_;
goto v___jp_863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* v_s_923_, lean_object* v_declName_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_923_, v_declName_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec_ref(v_s_923_);
return v_res_930_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_931_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
lean_ctor_set(v___x_936_, 2, v___x_935_);
lean_ctor_set(v___x_936_, 3, v___x_935_);
lean_ctor_set(v___x_936_, 4, v___x_934_);
lean_ctor_set(v___x_936_, 5, v___x_934_);
lean_ctor_set(v___x_936_, 6, v___x_934_);
lean_ctor_set(v___x_936_, 7, v___x_934_);
lean_ctor_set(v___x_936_, 8, v___x_934_);
lean_ctor_set(v___x_936_, 9, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_unsigned_to_nat(32u);
v___x_938_ = lean_mk_empty_array_with_capacity(v___x_937_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_940_ = ((size_t)5ULL);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_unsigned_to_nat(32u);
v___x_943_ = lean_mk_empty_array_with_capacity(v___x_942_);
v___x_944_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
v___x_945_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_943_);
lean_ctor_set(v___x_945_, 2, v___x_941_);
lean_ctor_set(v___x_945_, 3, v___x_941_);
lean_ctor_set_usize(v___x_945_, 4, v___x_940_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_946_ = lean_box(1);
v___x_947_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
v___x_948_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
lean_ctor_set(v___x_949_, 2, v___x_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* v_msgData_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; lean_object* v_env_955_; lean_object* v_options_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_954_ = lean_st_ref_get(v___y_952_);
v_env_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc_ref(v_env_955_);
lean_dec(v___x_954_);
v_options_956_ = lean_ctor_get(v___y_951_, 2);
v___x_957_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_958_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_956_);
v___x_959_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_959_, 0, v_env_955_);
lean_ctor_set(v___x_959_, 1, v___x_957_);
lean_ctor_set(v___x_959_, 2, v___x_958_);
lean_ctor_set(v___x_959_, 3, v_options_956_);
v___x_960_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v_msgData_950_);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object* v_msgData_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msgData_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_ref_971_; lean_object* v___x_972_; lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
v_ref_971_ = lean_ctor_get(v___y_968_, 5);
v___x_972_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msg_967_, v___y_968_, v___y_969_);
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_981_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
lean_inc(v_ref_971_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v_ref_971_);
lean_ctor_set(v___x_977_, 1, v_a_973_);
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 1);
lean_ctor_set(v___x_975_, 0, v___x_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object* v_msg_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
return v_res_986_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object* v_s_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v_env_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1004_ = lean_st_ref_get(v_a_1002_);
v_env_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc_ref(v_env_1005_);
lean_dec(v___x_1004_);
v___x_1006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
v___x_1007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5));
lean_inc_ref(v_s_1000_);
v___x_1008_ = l_Lean_Parser_runParserCategory(v_env_1005_, v___x_1006_, v_s_1000_, v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 1)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; 
lean_dec_ref(v_s_1000_);
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = l_Lean_Meta_Grind_getAttrKindCore(v_a_1009_, v_a_1001_, v_a_1002_);
return v___x_1010_;
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec_ref(v___x_1008_);
v___x_1011_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7);
v___x_1012_ = l_Lean_stringToMessageData(v_s_1000_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1013_, v_a_1001_, v_a_1002_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object* v_s_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(v_s_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object* v_00_u03b1_1020_, lean_object* v_msg_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_1021_, v___y_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_msg_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(v_00_u03b1_1026_, v_msg_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_ref_1038_; lean_object* v___x_1039_; lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1048_; 
v_ref_1038_ = lean_ctor_get(v___y_1035_, 5);
v___x_1039_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
lean_inc(v_ref_1038_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v_ref_1038_);
lean_ctor_set(v___x_1044_, 1, v_a_1040_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 1);
lean_ctor_set(v___x_1042_, 0, v___x_1044_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object* v_msg_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1055_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0));
v___x_1058_ = l_Lean_stringToMessageData(v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t v_minIndexable_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
if (v_minIndexable_1059_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1);
v___x_1068_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1067_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object* v_minIndexable_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
uint8_t v_minIndexable_boxed_1075_; lean_object* v_res_1076_; 
v_minIndexable_boxed_1075_ = lean_unbox(v_minIndexable_1069_);
v_res_1076_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_boxed_1075_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object* v_00_u03b1_1077_, lean_object* v_msg_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object* v_00_u03b1_1085_, lean_object* v_msg_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(v_00_u03b1_1085_, v_msg_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
return v_res_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1114_, lean_object* v_declHint_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v_env_1119_; uint8_t v___y_1121_; uint8_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1118_ = lean_st_ref_get(v___y_1116_);
v_env_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_ref(v_env_1119_);
lean_dec(v___x_1118_);
v___x_1177_ = l_Lean_Name_isAnonymous(v_declHint_1115_);
v___x_1178_ = lean_bool_not(v___x_1177_);
if (v___x_1178_ == 0)
{
v___y_1121_ = v___x_1178_;
goto v___jp_1120_;
}
else
{
uint8_t v_isExporting_1179_; 
v_isExporting_1179_ = lean_ctor_get_uint8(v_env_1119_, sizeof(void*)*8);
v___y_1121_ = v_isExporting_1179_;
goto v___jp_1120_;
}
v___jp_1120_:
{
if (v___y_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v_env_1119_);
lean_dec(v_declHint_1115_);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v_msg_1114_);
return v___x_1122_;
}
else
{
uint8_t v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1123_ = 0;
lean_inc_ref(v_env_1119_);
v___x_1124_ = l_Lean_Environment_setExporting(v_env_1119_, v___x_1123_);
lean_inc(v_declHint_1115_);
lean_inc_ref(v___x_1124_);
v___x_1125_ = l_Lean_Environment_contains(v___x_1124_, v_declHint_1115_, v___y_1121_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_dec_ref(v___x_1124_);
lean_dec_ref(v_env_1119_);
lean_dec(v_declHint_1115_);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_msg_1114_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v_c_1132_; lean_object* v___x_1133_; 
v___x_1127_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_1128_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
v___x_1129_ = l_Lean_Options_empty;
v___x_1130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1124_);
lean_ctor_set(v___x_1130_, 1, v___x_1127_);
lean_ctor_set(v___x_1130_, 2, v___x_1128_);
lean_ctor_set(v___x_1130_, 3, v___x_1129_);
lean_inc(v_declHint_1115_);
v___x_1131_ = l_Lean_MessageData_ofConstName(v_declHint_1115_, v___x_1123_);
v_c_1132_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1132_, 0, v___x_1130_);
lean_ctor_set(v_c_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1119_, v_declHint_1115_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref(v_env_1119_);
lean_dec(v_declHint_1115_);
v___x_1134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v_c_1132_);
v___x_1136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Lean_MessageData_note(v___x_1137_);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_msg_1114_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v_val_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1176_; 
v_val_1141_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1143_ = v___x_1133_;
v_isShared_1144_ = v_isSharedCheck_1176_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_val_1141_);
lean_dec(v___x_1133_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1176_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_mod_1148_; uint8_t v___x_1149_; 
v___x_1145_ = lean_box(0);
v___x_1146_ = l_Lean_Environment_header(v_env_1119_);
lean_dec_ref(v_env_1119_);
v___x_1147_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1146_);
v_mod_1148_ = lean_array_get(v___x_1145_, v___x_1147_, v_val_1141_);
lean_dec(v_val_1141_);
lean_dec_ref(v___x_1147_);
v___x_1149_ = l_Lean_isPrivateName(v_declHint_1115_);
lean_dec(v_declHint_1115_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1150_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v_c_1132_);
v___x_1152_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_MessageData_ofName(v_mod_1148_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_MessageData_note(v___x_1157_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_msg_1114_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1159_);
v___x_1161_ = v___x_1143_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1163_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v_c_1132_);
v___x_1165_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = l_Lean_MessageData_ofName(v_mod_1148_);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = l_Lean_MessageData_note(v___x_1170_);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v_msg_1114_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1172_);
v___x_1174_ = v___x_1143_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1180_, lean_object* v_declHint_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1180_, v_declHint_1181_, v___y_1182_);
lean_dec(v___y_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1185_, lean_object* v_declHint_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1202_; 
v___x_1192_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1185_, v_declHint_1186_, v___y_1190_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1197_ = l_Lean_unknownIdentifierMessageTag;
v___x_1198_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v_a_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1198_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1203_, lean_object* v_declHint_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1203_, v_declHint_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1211_, lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_fileName_1218_; lean_object* v_fileMap_1219_; lean_object* v_options_1220_; lean_object* v_currRecDepth_1221_; lean_object* v_maxRecDepth_1222_; lean_object* v_ref_1223_; lean_object* v_currNamespace_1224_; lean_object* v_openDecls_1225_; lean_object* v_initHeartbeats_1226_; lean_object* v_maxHeartbeats_1227_; lean_object* v_quotContext_1228_; lean_object* v_currMacroScope_1229_; uint8_t v_diag_1230_; lean_object* v_cancelTk_x3f_1231_; uint8_t v_suppressElabErrors_1232_; lean_object* v_inheritedTraceOptions_1233_; lean_object* v_ref_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_fileName_1218_ = lean_ctor_get(v___y_1215_, 0);
v_fileMap_1219_ = lean_ctor_get(v___y_1215_, 1);
v_options_1220_ = lean_ctor_get(v___y_1215_, 2);
v_currRecDepth_1221_ = lean_ctor_get(v___y_1215_, 3);
v_maxRecDepth_1222_ = lean_ctor_get(v___y_1215_, 4);
v_ref_1223_ = lean_ctor_get(v___y_1215_, 5);
v_currNamespace_1224_ = lean_ctor_get(v___y_1215_, 6);
v_openDecls_1225_ = lean_ctor_get(v___y_1215_, 7);
v_initHeartbeats_1226_ = lean_ctor_get(v___y_1215_, 8);
v_maxHeartbeats_1227_ = lean_ctor_get(v___y_1215_, 9);
v_quotContext_1228_ = lean_ctor_get(v___y_1215_, 10);
v_currMacroScope_1229_ = lean_ctor_get(v___y_1215_, 11);
v_diag_1230_ = lean_ctor_get_uint8(v___y_1215_, sizeof(void*)*14);
v_cancelTk_x3f_1231_ = lean_ctor_get(v___y_1215_, 12);
v_suppressElabErrors_1232_ = lean_ctor_get_uint8(v___y_1215_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1233_ = lean_ctor_get(v___y_1215_, 13);
v_ref_1234_ = l_Lean_replaceRef(v_ref_1211_, v_ref_1223_);
lean_inc_ref(v_inheritedTraceOptions_1233_);
lean_inc(v_cancelTk_x3f_1231_);
lean_inc(v_currMacroScope_1229_);
lean_inc(v_quotContext_1228_);
lean_inc(v_maxHeartbeats_1227_);
lean_inc(v_initHeartbeats_1226_);
lean_inc(v_openDecls_1225_);
lean_inc(v_currNamespace_1224_);
lean_inc(v_maxRecDepth_1222_);
lean_inc(v_currRecDepth_1221_);
lean_inc_ref(v_options_1220_);
lean_inc_ref(v_fileMap_1219_);
lean_inc_ref(v_fileName_1218_);
v___x_1235_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1235_, 0, v_fileName_1218_);
lean_ctor_set(v___x_1235_, 1, v_fileMap_1219_);
lean_ctor_set(v___x_1235_, 2, v_options_1220_);
lean_ctor_set(v___x_1235_, 3, v_currRecDepth_1221_);
lean_ctor_set(v___x_1235_, 4, v_maxRecDepth_1222_);
lean_ctor_set(v___x_1235_, 5, v_ref_1234_);
lean_ctor_set(v___x_1235_, 6, v_currNamespace_1224_);
lean_ctor_set(v___x_1235_, 7, v_openDecls_1225_);
lean_ctor_set(v___x_1235_, 8, v_initHeartbeats_1226_);
lean_ctor_set(v___x_1235_, 9, v_maxHeartbeats_1227_);
lean_ctor_set(v___x_1235_, 10, v_quotContext_1228_);
lean_ctor_set(v___x_1235_, 11, v_currMacroScope_1229_);
lean_ctor_set(v___x_1235_, 12, v_cancelTk_x3f_1231_);
lean_ctor_set(v___x_1235_, 13, v_inheritedTraceOptions_1233_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*14, v_diag_1230_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*14 + 1, v_suppressElabErrors_1232_);
v___x_1236_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1212_, v___y_1213_, v___y_1214_, v___x_1235_, v___y_1216_);
lean_dec_ref_known(v___x_1235_, 14);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1237_, lean_object* v_msg_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1237_, v_msg_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v_ref_1237_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1245_, lean_object* v_msg_1246_, lean_object* v_declHint_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; lean_object* v_a_1254_; lean_object* v___x_1255_; 
v___x_1253_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1246_, v_declHint_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1245_, v_a_1254_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1256_, lean_object* v_msg_1257_, lean_object* v_declHint_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1256_, v_msg_1257_, v_declHint_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v_ref_1256_);
return v_res_1264_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1268_, lean_object* v_constName_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1275_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1276_ = 0;
lean_inc(v_constName_1269_);
v___x_1277_ = l_Lean_MessageData_ofConstName(v_constName_1269_, v___x_1276_);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1275_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1268_, v___x_1280_, v_constName_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1282_, lean_object* v_constName_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1282_, v_constName_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v_ref_1282_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_ref_1296_; lean_object* v___x_1297_; 
v_ref_1296_ = lean_ctor_get(v___y_1293_, 5);
v___x_1297_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1296_, v_constName_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1305_, uint8_t v_skipRealize_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v_env_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_st_ref_get(v___y_1310_);
v_env_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_ref(v_env_1313_);
lean_dec(v___x_1312_);
lean_inc(v_constName_1305_);
v___x_1314_ = l_Lean_Environment_findAsync_x3f(v_env_1313_, v_constName_1305_, v_skipRealize_1306_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1305_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1315_;
}
else
{
lean_object* v_val_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v_constName_1305_);
v_val_1316_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1314_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_val_1316_);
lean_dec(v___x_1314_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 0);
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_val_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1324_, lean_object* v_skipRealize_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_skipRealize_boxed_1331_; lean_object* v_res_1332_; 
v_skipRealize_boxed_1331_ = lean_unbox(v_skipRealize_1325_);
v_res_1332_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1324_, v_skipRealize_boxed_1331_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; lean_object* v_env_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1336_ = lean_st_ref_get(v___y_1334_);
v_env_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc_ref(v_env_1337_);
lean_dec(v___x_1336_);
v___x_1338_ = l_Lean_getReducibilityStatusCore(v_env_1337_, v_declName_1333_);
v___x_1339_ = lean_box(v___x_1338_);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1341_, v___y_1342_);
lean_dec(v___y_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1367_; 
v___x_1351_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1345_, v___y_1349_);
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1367_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1367_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_unbox(v_a_1352_);
lean_dec(v_a_1352_);
if (v___x_1356_ == 0)
{
uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1357_ = 1;
v___x_1358_ = lean_box(v___x_1357_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1358_);
v___x_1360_ = v___x_1354_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1362_ = 0;
v___x_1363_ = lean_box(v___x_1362_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1363_);
v___x_1365_ = v___x_1354_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1374_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1386_ = l_Lean_stringToMessageData(v___x_1385_);
return v___x_1386_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1389_ = l_Lean_stringToMessageData(v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1390_, lean_object* v_id_1391_, lean_object* v_declName_1392_, lean_object* v_kind_1393_, uint8_t v_minIndexable_1394_, uint8_t v_suggest_1395_, uint8_t v_warn_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v___y_1403_; lean_object* v_thm_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; uint8_t v___x_1458_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___x_1658_; 
v___x_1458_ = 0;
lean_inc(v_declName_1392_);
v___x_1658_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1392_, v___x_1458_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; uint8_t v_kind_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v_kind_1660_ = lean_ctor_get_uint8(v_a_1659_, sizeof(void*)*3);
lean_dec(v_a_1659_);
switch(v_kind_1660_)
{
case 1:
{
v___y_1589_ = v_a_1397_;
v___y_1590_ = v_a_1398_;
v___y_1591_ = v_a_1399_;
v___y_1592_ = v_a_1400_;
goto v___jp_1588_;
}
case 2:
{
v___y_1589_ = v_a_1397_;
v___y_1590_ = v_a_1398_;
v___y_1591_ = v_a_1399_;
v___y_1592_ = v_a_1400_;
goto v___jp_1588_;
}
case 6:
{
v___y_1589_ = v_a_1397_;
v___y_1590_ = v_a_1398_;
v___y_1591_ = v_a_1399_;
v___y_1592_ = v_a_1400_;
goto v___jp_1588_;
}
case 0:
{
lean_object* v___x_1661_; 
lean_dec(v_id_1391_);
lean_inc(v_declName_1392_);
v___x_1661_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1392_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; uint8_t v___x_1663_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1663_ = lean_unbox(v_a_1662_);
lean_dec(v_a_1662_);
if (v___x_1663_ == 0)
{
v___y_1516_ = v_a_1397_;
v___y_1517_ = v_a_1398_;
v___y_1518_ = v_a_1399_;
v___y_1519_ = v_a_1400_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_kind_1393_);
lean_dec_ref(v_params_1390_);
v___x_1664_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1665_ = l_Lean_MessageData_ofConstName(v_declName_1392_, v___x_1458_);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1668_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_kind_1393_);
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1678_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1661_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1661_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
default: 
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_kind_1393_);
lean_dec(v_id_1391_);
lean_dec_ref(v_params_1390_);
v___x_1686_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1687_ = l_Lean_MessageData_ofConstName(v_declName_1392_, v___x_1458_);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1690_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
return v___x_1691_;
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_kind_1393_);
lean_dec(v_declName_1392_);
lean_dec(v_id_1391_);
lean_dec_ref(v_params_1390_);
v_a_1692_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1658_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1658_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
v___jp_1402_:
{
lean_object* v_config_1404_; lean_object* v_extensions_1405_; lean_object* v_extra_1406_; lean_object* v_extraInj_1407_; lean_object* v_extraFacts_1408_; lean_object* v_symPrios_1409_; lean_object* v_norm_1410_; lean_object* v_normProcs_1411_; lean_object* v_anchorRefs_x3f_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1421_; 
v_config_1404_ = lean_ctor_get(v_params_1390_, 0);
v_extensions_1405_ = lean_ctor_get(v_params_1390_, 1);
v_extra_1406_ = lean_ctor_get(v_params_1390_, 2);
v_extraInj_1407_ = lean_ctor_get(v_params_1390_, 3);
v_extraFacts_1408_ = lean_ctor_get(v_params_1390_, 4);
v_symPrios_1409_ = lean_ctor_get(v_params_1390_, 5);
v_norm_1410_ = lean_ctor_get(v_params_1390_, 6);
v_normProcs_1411_ = lean_ctor_get(v_params_1390_, 7);
v_anchorRefs_x3f_1412_ = lean_ctor_get(v_params_1390_, 8);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_params_1390_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1414_ = v_params_1390_;
v_isShared_1415_ = v_isSharedCheck_1421_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_anchorRefs_x3f_1412_);
lean_inc(v_normProcs_1411_);
lean_inc(v_norm_1410_);
lean_inc(v_symPrios_1409_);
lean_inc(v_extraFacts_1408_);
lean_inc(v_extraInj_1407_);
lean_inc(v_extra_1406_);
lean_inc(v_extensions_1405_);
lean_inc(v_config_1404_);
lean_dec(v_params_1390_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1421_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = l_Lean_PersistentArray_push___redArg(v_extra_1406_, v___y_1403_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 2, v___x_1416_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_config_1404_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_extensions_1405_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_extraInj_1407_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_extraFacts_1408_);
lean_ctor_set(v_reuseFailAlloc_1420_, 5, v_symPrios_1409_);
lean_ctor_set(v_reuseFailAlloc_1420_, 6, v_norm_1410_);
lean_ctor_set(v_reuseFailAlloc_1420_, 7, v_normProcs_1411_);
lean_ctor_set(v_reuseFailAlloc_1420_, 8, v_anchorRefs_x3f_1412_);
v___x_1418_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
}
v___jp_1422_:
{
if (v_warn_1396_ == 0)
{
lean_dec(v_declName_1392_);
v___y_1403_ = v_thm_1423_;
goto v___jp_1402_;
}
else
{
lean_object* v_extensions_1428_; lean_object* v_patterns_1429_; lean_object* v_origin_1430_; lean_object* v_cnstrs_1431_; uint8_t v___x_1432_; 
v_extensions_1428_ = lean_ctor_get(v_params_1390_, 1);
v_patterns_1429_ = lean_ctor_get(v_thm_1423_, 3);
v_origin_1430_ = lean_ctor_get(v_thm_1423_, 5);
v_cnstrs_1431_ = lean_ctor_get(v_thm_1423_, 7);
v___x_1432_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1428_, v_origin_1430_, v_patterns_1429_, v_cnstrs_1431_);
if (v___x_1432_ == 0)
{
lean_dec(v_declName_1392_);
v___y_1403_ = v_thm_1423_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1428_, v_declName_1392_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_dec_ref_known(v___x_1433_, 1);
v___y_1403_ = v_thm_1423_;
goto v___jp_1402_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec_ref(v_thm_1423_);
lean_dec_ref(v_params_1390_);
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
}
v___jp_1442_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1454_ = l_Lean_PersistentArray_push___redArg(v___y_1443_, v___y_1453_);
v___x_1455_ = l_Lean_PersistentArray_push___redArg(v___x_1454_, v___y_1444_);
v___x_1456_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1456_, 0, v___y_1451_);
lean_ctor_set(v___x_1456_, 1, v___y_1449_);
lean_ctor_set(v___x_1456_, 2, v___x_1455_);
lean_ctor_set(v___x_1456_, 3, v___y_1447_);
lean_ctor_set(v___x_1456_, 4, v___y_1446_);
lean_ctor_set(v___x_1456_, 5, v___y_1450_);
lean_ctor_set(v___x_1456_, 6, v___y_1448_);
lean_ctor_set(v___x_1456_, 7, v___y_1452_);
lean_ctor_set(v___x_1456_, 8, v___y_1445_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
v___jp_1459_:
{
lean_object* v___x_1464_; 
v___x_1464_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1394_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; 
lean_dec_ref_known(v___x_1464_, 1);
lean_inc(v_declName_1392_);
v___x_1465_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1392_, v___x_1458_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1498_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1498_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1498_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
if (lean_obj_tag(v_a_1466_) == 1)
{
lean_object* v_val_1470_; lean_object* v_config_1471_; lean_object* v_extensions_1472_; lean_object* v_extra_1473_; lean_object* v_extraInj_1474_; lean_object* v_extraFacts_1475_; lean_object* v_symPrios_1476_; lean_object* v_norm_1477_; lean_object* v_normProcs_1478_; lean_object* v_anchorRefs_x3f_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_declName_1392_);
v_val_1470_ = lean_ctor_get(v_a_1466_, 0);
lean_inc(v_val_1470_);
lean_dec_ref_known(v_a_1466_, 1);
v_config_1471_ = lean_ctor_get(v_params_1390_, 0);
v_extensions_1472_ = lean_ctor_get(v_params_1390_, 1);
v_extra_1473_ = lean_ctor_get(v_params_1390_, 2);
v_extraInj_1474_ = lean_ctor_get(v_params_1390_, 3);
v_extraFacts_1475_ = lean_ctor_get(v_params_1390_, 4);
v_symPrios_1476_ = lean_ctor_get(v_params_1390_, 5);
v_norm_1477_ = lean_ctor_get(v_params_1390_, 6);
v_normProcs_1478_ = lean_ctor_get(v_params_1390_, 7);
v_anchorRefs_x3f_1479_ = lean_ctor_get(v_params_1390_, 8);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_params_1390_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1481_ = v_params_1390_;
v_isShared_1482_ = v_isSharedCheck_1491_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_anchorRefs_x3f_1479_);
lean_inc(v_normProcs_1478_);
lean_inc(v_norm_1477_);
lean_inc(v_symPrios_1476_);
lean_inc(v_extraFacts_1475_);
lean_inc(v_extraInj_1474_);
lean_inc(v_extra_1473_);
lean_inc(v_extensions_1472_);
lean_inc(v_config_1471_);
lean_dec(v_params_1390_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1491_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1483_ = l_Lean_Array_toPArray_x27___redArg(v_val_1470_);
lean_dec(v_val_1470_);
v___x_1484_ = l_Lean_PersistentArray_append___redArg(v_extra_1473_, v___x_1483_);
lean_dec_ref(v___x_1483_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 2, v___x_1484_);
v___x_1486_ = v___x_1481_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_config_1471_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_extensions_1472_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_extraInj_1474_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_extraFacts_1475_);
lean_ctor_set(v_reuseFailAlloc_1490_, 5, v_symPrios_1476_);
lean_ctor_set(v_reuseFailAlloc_1490_, 6, v_norm_1477_);
lean_ctor_set(v_reuseFailAlloc_1490_, 7, v_normProcs_1478_);
lean_ctor_set(v_reuseFailAlloc_1490_, 8, v_anchorRefs_x3f_1479_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1488_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1486_);
v___x_1488_ = v___x_1468_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_del_object(v___x_1468_);
lean_dec(v_a_1466_);
lean_dec_ref(v_params_1390_);
v___x_1492_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1493_ = l_Lean_MessageData_ofConstName(v_declName_1392_, v___x_1458_);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1496_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
return v___x_1497_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1499_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1465_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1465_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1507_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1464_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1464_);
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
}
v___jp_1515_:
{
uint8_t v___x_1520_; uint8_t v___x_1521_; 
v___x_1520_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1393_);
v___x_1521_ = lean_bool_not(v___x_1520_);
if (v___x_1521_ == 0)
{
lean_dec(v_kind_1393_);
v___y_1460_ = v___y_1516_;
v___y_1461_ = v___y_1517_;
v___y_1462_ = v___y_1518_;
v___y_1463_ = v___y_1519_;
goto v___jp_1459_;
}
else
{
uint8_t v___x_1522_; uint8_t v___x_1523_; 
v___x_1522_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1393_);
lean_dec(v_kind_1393_);
v___x_1523_ = lean_bool_not(v___x_1522_);
if (v___x_1523_ == 0)
{
v___y_1460_ = v___y_1516_;
v___y_1461_ = v___y_1517_;
v___y_1462_ = v___y_1518_;
v___y_1463_ = v___y_1519_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v_params_1390_);
v___x_1524_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1525_ = l_Lean_MessageData_ofConstName(v_declName_1392_, v___x_1458_);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1528_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
v___jp_1538_:
{
lean_object* v_symPrios_1543_; lean_object* v___x_1544_; 
v_symPrios_1543_ = lean_ctor_get(v_params_1390_, 5);
lean_inc_ref(v_symPrios_1543_);
lean_inc(v_declName_1392_);
v___x_1544_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1392_, v_kind_1393_, v_symPrios_1543_, v___x_1458_, v_minIndexable_1394_, v___y_1540_, v___y_1542_, v___y_1541_, v___y_1539_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v_thm_1423_ = v_a_1545_;
v___y_1424_ = v___y_1540_;
v___y_1425_ = v___y_1542_;
v___y_1426_ = v___y_1541_;
v___y_1427_ = v___y_1539_;
goto v___jp_1422_;
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1546_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1544_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1544_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
v___jp_1554_:
{
if (v_suggest_1395_ == 0)
{
lean_dec(v_id_1391_);
v___y_1539_ = v___y_1558_;
v___y_1540_ = v___y_1555_;
v___y_1541_ = v___y_1557_;
v___y_1542_ = v___y_1556_;
goto v___jp_1538_;
}
else
{
lean_object* v_options_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; uint8_t v___x_1562_; 
v_options_1559_ = lean_ctor_get(v___y_1557_, 2);
v___x_1560_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1561_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_1559_, v___x_1560_);
v___x_1562_ = lean_bool_not(v___x_1561_);
if (v___x_1562_ == 0)
{
lean_dec(v_id_1391_);
v___y_1539_ = v___y_1558_;
v___y_1540_ = v___y_1555_;
v___y_1541_ = v___y_1557_;
v___y_1542_ = v___y_1556_;
goto v___jp_1538_;
}
else
{
lean_object* v_symPrios_1563_; lean_object* v___x_1564_; 
lean_dec(v_kind_1393_);
v_symPrios_1563_ = lean_ctor_get(v_params_1390_, 5);
lean_inc_ref(v_symPrios_1563_);
lean_inc(v_declName_1392_);
v___x_1564_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1391_, v_declName_1392_, v_symPrios_1563_, v_minIndexable_1394_, v_suggest_1395_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v_thm_1423_ = v_a_1565_;
v___y_1424_ = v___y_1555_;
v___y_1425_ = v___y_1556_;
v___y_1426_ = v___y_1557_;
v___y_1427_ = v___y_1558_;
goto v___jp_1422_;
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1566_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1564_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1564_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
v___jp_1574_:
{
lean_object* v___x_1579_; 
v___x_1579_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1394_, v___y_1575_, v___y_1578_, v___y_1577_, v___y_1576_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_dec_ref_known(v___x_1579_, 1);
v___y_1555_ = v___y_1575_;
v___y_1556_ = v___y_1578_;
v___y_1557_ = v___y_1577_;
v___y_1558_ = v___y_1576_;
goto v___jp_1554_;
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_kind_1393_);
lean_dec(v_declName_1392_);
lean_dec(v_id_1391_);
lean_dec_ref(v_params_1390_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
v___jp_1588_:
{
if (lean_obj_tag(v_kind_1393_) == 2)
{
uint8_t v_gen_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_id_1391_);
v_gen_1593_ = lean_ctor_get_uint8(v_kind_1393_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_kind_1393_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1595_ = v_kind_1393_;
v_isShared_1596_ = v_isSharedCheck_1657_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v_kind_1393_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1657_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; 
v___x_1597_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1394_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_config_1598_; lean_object* v_extensions_1599_; lean_object* v_extra_1600_; lean_object* v_extraInj_1601_; lean_object* v_extraFacts_1602_; lean_object* v_symPrios_1603_; lean_object* v_norm_1604_; lean_object* v_normProcs_1605_; lean_object* v_anchorRefs_x3f_1606_; lean_object* v___x_1608_; 
lean_dec_ref_known(v___x_1597_, 1);
v_config_1598_ = lean_ctor_get(v_params_1390_, 0);
lean_inc_ref(v_config_1598_);
v_extensions_1599_ = lean_ctor_get(v_params_1390_, 1);
lean_inc_ref(v_extensions_1599_);
v_extra_1600_ = lean_ctor_get(v_params_1390_, 2);
lean_inc_ref(v_extra_1600_);
v_extraInj_1601_ = lean_ctor_get(v_params_1390_, 3);
lean_inc_ref(v_extraInj_1601_);
v_extraFacts_1602_ = lean_ctor_get(v_params_1390_, 4);
lean_inc_ref(v_extraFacts_1602_);
v_symPrios_1603_ = lean_ctor_get(v_params_1390_, 5);
lean_inc_ref(v_symPrios_1603_);
v_norm_1604_ = lean_ctor_get(v_params_1390_, 6);
lean_inc_ref(v_norm_1604_);
v_normProcs_1605_ = lean_ctor_get(v_params_1390_, 7);
lean_inc_ref(v_normProcs_1605_);
v_anchorRefs_x3f_1606_ = lean_ctor_get(v_params_1390_, 8);
lean_inc(v_anchorRefs_x3f_1606_);
lean_dec_ref(v_params_1390_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 0);
v___x_1608_ = v___x_1595_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1648_, 0, v_gen_1593_);
v___x_1608_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; 
lean_inc_ref(v_symPrios_1603_);
lean_inc(v_declName_1392_);
v___x_1609_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1392_, v___x_1608_, v_symPrios_1603_, v___x_1458_, v___x_1458_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1611_, 0, v_gen_1593_);
lean_inc_ref(v_symPrios_1603_);
lean_inc(v_declName_1392_);
v___x_1612_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1392_, v___x_1611_, v_symPrios_1603_, v___x_1458_, v___x_1458_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1612_) == 0)
{
if (v_warn_1396_ == 0)
{
lean_object* v_a_1613_; 
lean_dec(v_declName_1392_);
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___y_1443_ = v_extra_1600_;
v___y_1444_ = v_a_1613_;
v___y_1445_ = v_anchorRefs_x3f_1606_;
v___y_1446_ = v_extraFacts_1602_;
v___y_1447_ = v_extraInj_1601_;
v___y_1448_ = v_norm_1604_;
v___y_1449_ = v_extensions_1599_;
v___y_1450_ = v_symPrios_1603_;
v___y_1451_ = v_config_1598_;
v___y_1452_ = v_normProcs_1605_;
v___y_1453_ = v_a_1610_;
goto v___jp_1442_;
}
else
{
lean_object* v_a_1614_; lean_object* v_patterns_1615_; lean_object* v_origin_1616_; lean_object* v_cnstrs_1617_; uint8_t v___x_1618_; 
v_a_1614_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1612_, 1);
v_patterns_1615_ = lean_ctor_get(v_a_1610_, 3);
v_origin_1616_ = lean_ctor_get(v_a_1610_, 5);
v_cnstrs_1617_ = lean_ctor_get(v_a_1610_, 7);
v___x_1618_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1599_, v_origin_1616_, v_patterns_1615_, v_cnstrs_1617_);
if (v___x_1618_ == 0)
{
lean_dec(v_declName_1392_);
v___y_1443_ = v_extra_1600_;
v___y_1444_ = v_a_1614_;
v___y_1445_ = v_anchorRefs_x3f_1606_;
v___y_1446_ = v_extraFacts_1602_;
v___y_1447_ = v_extraInj_1601_;
v___y_1448_ = v_norm_1604_;
v___y_1449_ = v_extensions_1599_;
v___y_1450_ = v_symPrios_1603_;
v___y_1451_ = v_config_1598_;
v___y_1452_ = v_normProcs_1605_;
v___y_1453_ = v_a_1610_;
goto v___jp_1442_;
}
else
{
lean_object* v_patterns_1619_; lean_object* v_origin_1620_; lean_object* v_cnstrs_1621_; uint8_t v___x_1622_; 
v_patterns_1619_ = lean_ctor_get(v_a_1614_, 3);
v_origin_1620_ = lean_ctor_get(v_a_1614_, 5);
v_cnstrs_1621_ = lean_ctor_get(v_a_1614_, 7);
v___x_1622_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1599_, v_origin_1620_, v_patterns_1619_, v_cnstrs_1621_);
if (v___x_1622_ == 0)
{
lean_dec(v_declName_1392_);
v___y_1443_ = v_extra_1600_;
v___y_1444_ = v_a_1614_;
v___y_1445_ = v_anchorRefs_x3f_1606_;
v___y_1446_ = v_extraFacts_1602_;
v___y_1447_ = v_extraInj_1601_;
v___y_1448_ = v_norm_1604_;
v___y_1449_ = v_extensions_1599_;
v___y_1450_ = v_symPrios_1603_;
v___y_1451_ = v_config_1598_;
v___y_1452_ = v_normProcs_1605_;
v___y_1453_ = v_a_1610_;
goto v___jp_1442_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1599_, v_declName_1392_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_dec_ref_known(v___x_1623_, 1);
v___y_1443_ = v_extra_1600_;
v___y_1444_ = v_a_1614_;
v___y_1445_ = v_anchorRefs_x3f_1606_;
v___y_1446_ = v_extraFacts_1602_;
v___y_1447_ = v_extraInj_1601_;
v___y_1448_ = v_norm_1604_;
v___y_1449_ = v_extensions_1599_;
v___y_1450_ = v_symPrios_1603_;
v___y_1451_ = v_config_1598_;
v___y_1452_ = v_normProcs_1605_;
v___y_1453_ = v_a_1610_;
goto v___jp_1442_;
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_a_1614_);
lean_dec(v_a_1610_);
lean_dec(v_anchorRefs_x3f_1606_);
lean_dec_ref(v_normProcs_1605_);
lean_dec_ref(v_norm_1604_);
lean_dec_ref(v_symPrios_1603_);
lean_dec_ref(v_extraFacts_1602_);
lean_dec_ref(v_extraInj_1601_);
lean_dec_ref(v_extra_1600_);
lean_dec_ref(v_extensions_1599_);
lean_dec_ref(v_config_1598_);
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v_a_1610_);
lean_dec(v_anchorRefs_x3f_1606_);
lean_dec_ref(v_normProcs_1605_);
lean_dec_ref(v_norm_1604_);
lean_dec_ref(v_symPrios_1603_);
lean_dec_ref(v_extraFacts_1602_);
lean_dec_ref(v_extraInj_1601_);
lean_dec_ref(v_extra_1600_);
lean_dec_ref(v_extensions_1599_);
lean_dec_ref(v_config_1598_);
lean_dec(v_declName_1392_);
v_a_1632_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1612_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1612_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_anchorRefs_x3f_1606_);
lean_dec_ref(v_normProcs_1605_);
lean_dec_ref(v_norm_1604_);
lean_dec_ref(v_symPrios_1603_);
lean_dec_ref(v_extraFacts_1602_);
lean_dec_ref(v_extraInj_1601_);
lean_dec_ref(v_extra_1600_);
lean_dec_ref(v_extensions_1599_);
lean_dec_ref(v_config_1598_);
lean_dec(v_declName_1392_);
v_a_1640_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1609_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1609_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_del_object(v___x_1595_);
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1649_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1597_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1597_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
else
{
switch(lean_obj_tag(v_kind_1393_))
{
case 0:
{
v___y_1575_ = v___y_1589_;
v___y_1576_ = v___y_1592_;
v___y_1577_ = v___y_1591_;
v___y_1578_ = v___y_1590_;
goto v___jp_1574_;
}
case 1:
{
v___y_1575_ = v___y_1589_;
v___y_1576_ = v___y_1592_;
v___y_1577_ = v___y_1591_;
v___y_1578_ = v___y_1590_;
goto v___jp_1574_;
}
default: 
{
v___y_1555_ = v___y_1589_;
v___y_1556_ = v___y_1590_;
v___y_1557_ = v___y_1591_;
v___y_1558_ = v___y_1592_;
goto v___jp_1554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* v_params_1700_, lean_object* v_id_1701_, lean_object* v_declName_1702_, lean_object* v_kind_1703_, lean_object* v_minIndexable_1704_, lean_object* v_suggest_1705_, lean_object* v_warn_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
uint8_t v_minIndexable_boxed_1712_; uint8_t v_suggest_boxed_1713_; uint8_t v_warn_boxed_1714_; lean_object* v_res_1715_; 
v_minIndexable_boxed_1712_ = lean_unbox(v_minIndexable_1704_);
v_suggest_boxed_1713_ = lean_unbox(v_suggest_1705_);
v_warn_boxed_1714_ = lean_unbox(v_warn_1706_);
v_res_1715_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1700_, v_id_1701_, v_declName_1702_, v_kind_1703_, v_minIndexable_boxed_1712_, v_suggest_boxed_1713_, v_warn_boxed_1714_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* v_declName_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1716_, v___y_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* v_declName_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1730_, lean_object* v_constName_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1738_, lean_object* v_constName_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(v_00_u03b1_1738_, v_constName_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1746_, lean_object* v_ref_1747_, lean_object* v_constName_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1747_, v_constName_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1755_, lean_object* v_ref_1756_, lean_object* v_constName_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1755_, v_ref_1756_, v_constName_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v_ref_1756_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1764_, lean_object* v_ref_1765_, lean_object* v_msg_1766_, lean_object* v_declHint_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1765_, v_msg_1766_, v_declHint_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_ref_1775_, lean_object* v_msg_1776_, lean_object* v_declHint_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1774_, v_ref_1775_, v_msg_1776_, v_declHint_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v_ref_1775_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1784_, lean_object* v_declHint_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1784_, v_declHint_1785_, v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1792_, lean_object* v_declHint_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1792_, v_declHint_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1800_, lean_object* v_ref_1801_, lean_object* v_msg_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1801_, v_msg_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1809_, lean_object* v_ref_1810_, lean_object* v_msg_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1809_, v_ref_1810_, v_msg_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v_ref_1810_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1820_, lean_object* v_val_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v_config_1825_; lean_object* v_extensions_1826_; lean_object* v_extra_1827_; lean_object* v_extraInj_1828_; lean_object* v_extraFacts_1829_; lean_object* v_symPrios_1830_; lean_object* v_norm_1831_; lean_object* v_normProcs_1832_; lean_object* v_anchorRefs_x3f_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1863_; 
v_config_1825_ = lean_ctor_get(v_params_1820_, 0);
v_extensions_1826_ = lean_ctor_get(v_params_1820_, 1);
v_extra_1827_ = lean_ctor_get(v_params_1820_, 2);
v_extraInj_1828_ = lean_ctor_get(v_params_1820_, 3);
v_extraFacts_1829_ = lean_ctor_get(v_params_1820_, 4);
v_symPrios_1830_ = lean_ctor_get(v_params_1820_, 5);
v_norm_1831_ = lean_ctor_get(v_params_1820_, 6);
v_normProcs_1832_ = lean_ctor_get(v_params_1820_, 7);
v_anchorRefs_x3f_1833_ = lean_ctor_get(v_params_1820_, 8);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_params_1820_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1835_ = v_params_1820_;
v_isShared_1836_ = v_isSharedCheck_1863_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_anchorRefs_x3f_1833_);
lean_inc(v_normProcs_1832_);
lean_inc(v_norm_1831_);
lean_inc(v_symPrios_1830_);
lean_inc(v_extraFacts_1829_);
lean_inc(v_extraInj_1828_);
lean_inc(v_extra_1827_);
lean_inc(v_extensions_1826_);
lean_inc(v_config_1825_);
lean_dec(v_params_1820_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1863_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___y_1838_; 
if (lean_obj_tag(v_anchorRefs_x3f_1833_) == 0)
{
lean_object* v___x_1861_; 
v___x_1861_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1838_ = v___x_1861_;
goto v___jp_1837_;
}
else
{
lean_object* v_val_1862_; 
v_val_1862_ = lean_ctor_get(v_anchorRefs_x3f_1833_, 0);
lean_inc(v_val_1862_);
lean_dec_ref_known(v_anchorRefs_x3f_1833_, 1);
v___y_1838_ = v_val_1862_;
goto v___jp_1837_;
}
v___jp_1837_:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1852_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1852_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1852_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1844_ = lean_array_push(v___y_1838_, v_a_1840_);
v___x_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 8, v___x_1845_);
v___x_1847_ = v___x_1835_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_config_1825_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_extensions_1826_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_extra_1827_);
lean_ctor_set(v_reuseFailAlloc_1851_, 3, v_extraInj_1828_);
lean_ctor_set(v_reuseFailAlloc_1851_, 4, v_extraFacts_1829_);
lean_ctor_set(v_reuseFailAlloc_1851_, 5, v_symPrios_1830_);
lean_ctor_set(v_reuseFailAlloc_1851_, 6, v_norm_1831_);
lean_ctor_set(v_reuseFailAlloc_1851_, 7, v_normProcs_1832_);
lean_ctor_set(v_reuseFailAlloc_1851_, 8, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1847_);
v___x_1849_ = v___x_1842_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v___y_1838_);
lean_del_object(v___x_1835_);
lean_dec_ref(v_normProcs_1832_);
lean_dec_ref(v_norm_1831_);
lean_dec_ref(v_symPrios_1830_);
lean_dec_ref(v_extraFacts_1829_);
lean_dec_ref(v_extraInj_1828_);
lean_dec_ref(v_extra_1827_);
lean_dec_ref(v_extensions_1826_);
lean_dec_ref(v_config_1825_);
v_a_1853_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1839_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1839_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_1864_, lean_object* v_val_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1864_, v_val_1865_, v_a_1866_, v_a_1867_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_val_1865_);
return v_res_1869_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_1872_ = l_Lean_stringToMessageData(v___x_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_config_1877_; uint8_t v_revert_1878_; 
v_config_1877_ = lean_ctor_get(v_params_1873_, 0);
v_revert_1878_ = lean_ctor_get_uint8(v_config_1877_, sizeof(void*)*13 + 29);
if (v_revert_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_box(0);
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_1882_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1881_, v_a_1874_, v_a_1875_);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec_ref(v_params_1883_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_1888_, lean_object* v___y_1889_){
_start:
{
uint8_t v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = l_Lean_Expr_hasMVar(v_e_1888_);
v___x_1892_ = lean_bool_not(v___x_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v_mctx_1894_; lean_object* v___x_1895_; lean_object* v_fst_1896_; lean_object* v_snd_1897_; lean_object* v___x_1898_; lean_object* v_cache_1899_; lean_object* v_zetaDeltaFVarIds_1900_; lean_object* v_postponed_1901_; lean_object* v_diag_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1911_; 
v___x_1893_ = lean_st_ref_get(v___y_1889_);
v_mctx_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc_ref(v_mctx_1894_);
lean_dec(v___x_1893_);
v___x_1895_ = l_Lean_instantiateMVarsCore(v_mctx_1894_, v_e_1888_);
v_fst_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_fst_1896_);
v_snd_1897_ = lean_ctor_get(v___x_1895_, 1);
lean_inc(v_snd_1897_);
lean_dec_ref(v___x_1895_);
v___x_1898_ = lean_st_ref_take(v___y_1889_);
v_cache_1899_ = lean_ctor_get(v___x_1898_, 1);
v_zetaDeltaFVarIds_1900_ = lean_ctor_get(v___x_1898_, 2);
v_postponed_1901_ = lean_ctor_get(v___x_1898_, 3);
v_diag_1902_ = lean_ctor_get(v___x_1898_, 4);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v___x_1898_, 0);
lean_dec(v_unused_1912_);
v___x_1904_ = v___x_1898_;
v_isShared_1905_ = v_isSharedCheck_1911_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_diag_1902_);
lean_inc(v_postponed_1901_);
lean_inc(v_zetaDeltaFVarIds_1900_);
lean_inc(v_cache_1899_);
lean_dec(v___x_1898_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1911_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v_snd_1897_);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_snd_1897_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_cache_1899_);
lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_zetaDeltaFVarIds_1900_);
lean_ctor_set(v_reuseFailAlloc_1910_, 3, v_postponed_1901_);
lean_ctor_set(v_reuseFailAlloc_1910_, 4, v_diag_1902_);
v___x_1907_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_st_ref_set(v___y_1889_, v___x_1907_);
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_fst_1896_);
return v___x_1909_;
}
}
}
else
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_e_1888_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1914_, v___y_1915_);
lean_dec(v___y_1915_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1918_, v___y_1922_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(lean_object* v_p_1938_, lean_object* v_term_1939_, lean_object* v___x_1940_, uint8_t v___x_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_fileName_1949_; lean_object* v_fileMap_1950_; lean_object* v_options_1951_; lean_object* v_currRecDepth_1952_; lean_object* v_maxRecDepth_1953_; lean_object* v_ref_1954_; lean_object* v_currNamespace_1955_; lean_object* v_openDecls_1956_; lean_object* v_initHeartbeats_1957_; lean_object* v_maxHeartbeats_1958_; lean_object* v_quotContext_1959_; lean_object* v_currMacroScope_1960_; uint8_t v_diag_1961_; lean_object* v_cancelTk_x3f_1962_; uint8_t v_suppressElabErrors_1963_; lean_object* v_inheritedTraceOptions_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_2032_; 
v_fileName_1949_ = lean_ctor_get(v___y_1946_, 0);
v_fileMap_1950_ = lean_ctor_get(v___y_1946_, 1);
v_options_1951_ = lean_ctor_get(v___y_1946_, 2);
v_currRecDepth_1952_ = lean_ctor_get(v___y_1946_, 3);
v_maxRecDepth_1953_ = lean_ctor_get(v___y_1946_, 4);
v_ref_1954_ = lean_ctor_get(v___y_1946_, 5);
v_currNamespace_1955_ = lean_ctor_get(v___y_1946_, 6);
v_openDecls_1956_ = lean_ctor_get(v___y_1946_, 7);
v_initHeartbeats_1957_ = lean_ctor_get(v___y_1946_, 8);
v_maxHeartbeats_1958_ = lean_ctor_get(v___y_1946_, 9);
v_quotContext_1959_ = lean_ctor_get(v___y_1946_, 10);
v_currMacroScope_1960_ = lean_ctor_get(v___y_1946_, 11);
v_diag_1961_ = lean_ctor_get_uint8(v___y_1946_, sizeof(void*)*14);
v_cancelTk_x3f_1962_ = lean_ctor_get(v___y_1946_, 12);
v_suppressElabErrors_1963_ = lean_ctor_get_uint8(v___y_1946_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1964_ = lean_ctor_get(v___y_1946_, 13);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___y_1946_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_1966_ = v___y_1946_;
v_isShared_1967_ = v_isSharedCheck_2032_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_inheritedTraceOptions_1964_);
lean_inc(v_cancelTk_x3f_1962_);
lean_inc(v_currMacroScope_1960_);
lean_inc(v_quotContext_1959_);
lean_inc(v_maxHeartbeats_1958_);
lean_inc(v_initHeartbeats_1957_);
lean_inc(v_openDecls_1956_);
lean_inc(v_currNamespace_1955_);
lean_inc(v_ref_1954_);
lean_inc(v_maxRecDepth_1953_);
lean_inc(v_currRecDepth_1952_);
lean_inc(v_options_1951_);
lean_inc(v_fileMap_1950_);
lean_inc(v_fileName_1949_);
lean_dec(v___y_1946_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_2032_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_ref_1968_; lean_object* v___x_1970_; 
v_ref_1968_ = l_Lean_replaceRef(v_p_1938_, v_ref_1954_);
lean_dec(v_ref_1954_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 5, v_ref_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_fileName_1949_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_fileMap_1950_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v_options_1951_);
lean_ctor_set(v_reuseFailAlloc_2031_, 3, v_currRecDepth_1952_);
lean_ctor_set(v_reuseFailAlloc_2031_, 4, v_maxRecDepth_1953_);
lean_ctor_set(v_reuseFailAlloc_2031_, 5, v_ref_1968_);
lean_ctor_set(v_reuseFailAlloc_2031_, 6, v_currNamespace_1955_);
lean_ctor_set(v_reuseFailAlloc_2031_, 7, v_openDecls_1956_);
lean_ctor_set(v_reuseFailAlloc_2031_, 8, v_initHeartbeats_1957_);
lean_ctor_set(v_reuseFailAlloc_2031_, 9, v_maxHeartbeats_1958_);
lean_ctor_set(v_reuseFailAlloc_2031_, 10, v_quotContext_1959_);
lean_ctor_set(v_reuseFailAlloc_2031_, 11, v_currMacroScope_1960_);
lean_ctor_set(v_reuseFailAlloc_2031_, 12, v_cancelTk_x3f_1962_);
lean_ctor_set(v_reuseFailAlloc_2031_, 13, v_inheritedTraceOptions_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_2031_, sizeof(void*)*14, v_diag_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_2031_, sizeof(void*)*14 + 1, v_suppressElabErrors_1963_);
v___x_1970_ = v_reuseFailAlloc_2031_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_Elab_Term_elabTerm(v_term_1939_, v___x_1940_, v___x_1941_, v___x_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___x_1970_, v___y_1947_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v___x_1973_ = 1;
v___x_1974_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1973_, v___x_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___x_1970_, v___y_1947_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v___x_1975_; lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2014_; 
lean_dec_ref_known(v___x_1974_, 1);
v___x_1975_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_1972_, v___y_1945_);
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_2014_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2014_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
uint8_t v___x_1980_; 
v___x_1980_ = l_Lean_Expr_hasSyntheticSorry(v_a_1976_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = l_Lean_Expr_eta(v_a_1976_);
v___x_1982_ = l_Lean_Expr_hasMVar(v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
lean_dec_ref(v___x_1970_);
v___x_1983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0));
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v___x_1981_);
v___x_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1985_);
v___x_1987_ = v___x_1978_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
else
{
lean_object* v___x_1989_; 
lean_del_object(v___x_1978_);
v___x_1989_ = l_Lean_Meta_abstractMVars(v___x_1981_, v___x_1941_, v___y_1944_, v___y_1945_, v___x_1970_, v___y_1947_);
lean_dec_ref(v___x_1970_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2001_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2001_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2001_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_paramNames_1994_; lean_object* v_expr_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
v_paramNames_1994_ = lean_ctor_get(v_a_1990_, 0);
lean_inc_ref(v_paramNames_1994_);
v_expr_1995_ = lean_ctor_get(v_a_1990_, 2);
lean_inc_ref(v_expr_1995_);
lean_dec(v_a_1990_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v_paramNames_1994_);
lean_ctor_set(v___x_1996_, 1, v_expr_1995_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1997_);
v___x_1999_ = v___x_1992_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_a_2002_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1989_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1989_);
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
else
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
lean_dec(v_a_1976_);
lean_dec_ref(v___x_1970_);
v___x_2010_ = lean_box(0);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_2010_);
v___x_2012_ = v___x_1978_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_a_1972_);
lean_dec_ref(v___x_1970_);
v_a_2015_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1974_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1974_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v___x_1970_);
v_a_2023_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1971_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1971_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v_p_2033_, lean_object* v_term_2034_, lean_object* v___x_2035_, lean_object* v___x_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
uint8_t v___x_13872__boxed_2044_; lean_object* v_res_2045_; 
v___x_13872__boxed_2044_ = lean_unbox(v___x_2036_);
v_res_2045_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v_p_2033_, v_term_2034_, v___x_2035_, v___x_13872__boxed_2044_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v_p_2033_);
return v_res_2045_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2));
v___x_2051_ = l_Lean_stringToMessageData(v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_params_2052_, lean_object* v_p_2053_, lean_object* v_fst_2054_, lean_object* v_snd_2055_, uint8_t v___x_2056_, uint8_t v_minIndexable_2057_, lean_object* v_kind_2058_, lean_object* v_idx_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_symPrios_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; 
v_symPrios_2065_ = lean_ctor_get(v_params_2052_, 5);
lean_inc_ref(v_symPrios_2065_);
lean_dec_ref(v_params_2052_);
v___x_2066_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1));
v___x_2067_ = lean_name_append_index_after(v___x_2066_, v_idx_2059_);
v___x_2068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v_p_2053_);
v___x_2069_ = 0;
v___x_2070_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2068_, v_fst_2054_, v_snd_2055_, v_kind_2058_, v_symPrios_2065_, v___x_2056_, v___x_2069_, v_minIndexable_2057_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2081_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2081_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2081_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
if (lean_obj_tag(v_a_2071_) == 1)
{
lean_object* v_val_2075_; lean_object* v___x_2077_; 
v_val_2075_ = lean_ctor_get(v_a_2071_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v_a_2071_, 1);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v_val_2075_);
v___x_2077_ = v___x_2073_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_val_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_del_object(v___x_2073_);
lean_dec(v_a_2071_);
v___x_2079_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3);
v___x_2080_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2079_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
return v___x_2080_;
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2070_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2070_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_params_2090_, lean_object* v_p_2091_, lean_object* v_fst_2092_, lean_object* v_snd_2093_, lean_object* v___x_2094_, lean_object* v_minIndexable_2095_, lean_object* v_kind_2096_, lean_object* v_idx_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
uint8_t v___x_14046__boxed_2103_; uint8_t v_minIndexable_boxed_2104_; lean_object* v_res_2105_; 
v___x_14046__boxed_2103_ = lean_unbox(v___x_2094_);
v_minIndexable_boxed_2104_ = lean_unbox(v_minIndexable_2095_);
v_res_2105_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_params_2090_, v_p_2091_, v_fst_2092_, v_snd_2093_, v___x_14046__boxed_2103_, v_minIndexable_boxed_2104_, v_kind_2096_, v_idx_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
return v_res_2105_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_box(1);
v___x_2107_ = l_Lean_MessageData_ofFormat(v___x_2106_);
return v___x_2107_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2));
v___x_2112_ = l_Lean_MessageData_ofFormat(v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(lean_object* v_x_2113_, lean_object* v_x_2114_){
_start:
{
if (lean_obj_tag(v_x_2114_) == 0)
{
return v_x_2113_;
}
else
{
lean_object* v_head_2115_; lean_object* v_tail_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2138_; 
v_head_2115_ = lean_ctor_get(v_x_2114_, 0);
v_tail_2116_ = lean_ctor_get(v_x_2114_, 1);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_x_2114_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2118_ = v_x_2114_;
v_isShared_2119_ = v_isSharedCheck_2138_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_tail_2116_);
lean_inc(v_head_2115_);
lean_dec(v_x_2114_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2138_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_before_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2136_; 
v_before_2120_ = lean_ctor_get(v_head_2115_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_head_2115_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; 
v_unused_2137_ = lean_ctor_get(v_head_2115_, 1);
lean_dec(v_unused_2137_);
v___x_2122_ = v_head_2115_;
v_isShared_2123_ = v_isSharedCheck_2136_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_before_2120_);
lean_dec(v_head_2115_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2136_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2123_ == 0)
{
lean_ctor_set_tag(v___x_2122_, 7);
lean_ctor_set(v___x_2122_, 1, v___x_2124_);
lean_ctor_set(v___x_2122_, 0, v_x_2113_);
v___x_2126_ = v___x_2122_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_x_2113_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3);
if (v_isShared_2119_ == 0)
{
lean_ctor_set_tag(v___x_2118_, 7);
lean_ctor_set(v___x_2118_, 1, v___x_2127_);
lean_ctor_set(v___x_2118_, 0, v___x_2126_);
v___x_2129_ = v___x_2118_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = l_Lean_MessageData_ofSyntax(v_before_2120_);
v___x_2131_ = l_Lean_indentD(v___x_2130_);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2129_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v_x_2113_ = v___x_2132_;
v_x_2114_ = v_tail_2116_;
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
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1));
v___x_2143_ = l_Lean_MessageData_ofFormat(v___x_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(lean_object* v_msgData_2144_, lean_object* v_macroStack_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_options_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; uint8_t v___x_2151_; 
v_options_2148_ = lean_ctor_get(v___y_2146_, 2);
v___x_2149_ = l_Lean_Elab_pp_macroStack;
v___x_2150_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2148_, v___x_2149_);
v___x_2151_ = lean_bool_not(v___x_2150_);
if (v___x_2151_ == 0)
{
if (lean_obj_tag(v_macroStack_2145_) == 0)
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v_msgData_2144_);
return v___x_2152_;
}
else
{
lean_object* v_head_2153_; lean_object* v_after_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2169_; 
v_head_2153_ = lean_ctor_get(v_macroStack_2145_, 0);
lean_inc(v_head_2153_);
v_after_2154_ = lean_ctor_get(v_head_2153_, 1);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_head_2153_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v_head_2153_, 0);
lean_dec(v_unused_2170_);
v___x_2156_ = v_head_2153_;
v_isShared_2157_ = v_isSharedCheck_2169_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_after_2154_);
lean_dec(v_head_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2169_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2157_ == 0)
{
lean_ctor_set_tag(v___x_2156_, 7);
lean_ctor_set(v___x_2156_, 1, v___x_2158_);
lean_ctor_set(v___x_2156_, 0, v_msgData_2144_);
v___x_2160_ = v___x_2156_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_msgData_2144_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v_msgData_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2161_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = l_Lean_MessageData_ofSyntax(v_after_2154_);
v___x_2164_ = l_Lean_indentD(v___x_2163_);
v_msgData_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2165_, 0, v___x_2162_);
lean_ctor_set(v_msgData_2165_, 1, v___x_2164_);
v___x_2166_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(v_msgData_2165_, v_macroStack_2145_);
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
return v___x_2167_;
}
}
}
}
else
{
lean_object* v___x_2171_; 
lean_dec(v_macroStack_2145_);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v_msgData_2144_);
return v___x_2171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2172_, lean_object* v_macroStack_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2172_, v_macroStack_2173_, v___y_2174_);
lean_dec_ref(v___y_2174_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(lean_object* v_msg_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_ref_2185_; lean_object* v___x_2186_; lean_object* v_a_2187_; lean_object* v_macroStack_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2199_; 
v_ref_2185_ = lean_ctor_get(v___y_2182_, 5);
v___x_2186_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2177_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref(v___x_2186_);
v_macroStack_2188_ = lean_ctor_get(v___y_2178_, 1);
v___x_2189_ = l_Lean_Elab_getBetterRef(v_ref_2185_, v_macroStack_2188_);
lean_inc(v_macroStack_2188_);
v___x_2190_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_a_2187_, v_macroStack_2188_, v___y_2182_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2189_);
lean_ctor_set(v___x_2195_, 1, v_a_2191_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set_tag(v___x_2193_, 1);
lean_ctor_set(v___x_2193_, 0, v___x_2195_);
v___x_2197_ = v___x_2193_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v_msg_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v_res_2208_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2211_ = l_Lean_stringToMessageData(v___x_2210_);
return v___x_2211_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2214_ = l_Lean_stringToMessageData(v___x_2213_);
return v___x_2214_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2217_ = l_Lean_stringToMessageData(v___x_2216_);
return v___x_2217_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2223_, lean_object* v_p_2224_, lean_object* v_mod_x3f_2225_, lean_object* v_term_2226_, uint8_t v_minIndexable_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2298_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v_kind_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v_fileName_2533_; lean_object* v_fileMap_2534_; lean_object* v_options_2535_; lean_object* v_currRecDepth_2536_; lean_object* v_maxRecDepth_2537_; lean_object* v_ref_2538_; lean_object* v_currNamespace_2539_; lean_object* v_openDecls_2540_; lean_object* v_initHeartbeats_2541_; lean_object* v_maxHeartbeats_2542_; lean_object* v_quotContext_2543_; lean_object* v_currMacroScope_2544_; uint8_t v_diag_2545_; lean_object* v_cancelTk_x3f_2546_; uint8_t v_suppressElabErrors_2547_; lean_object* v_inheritedTraceOptions_2548_; lean_object* v_ref_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_fileName_2533_ = lean_ctor_get(v_a_2232_, 0);
v_fileMap_2534_ = lean_ctor_get(v_a_2232_, 1);
v_options_2535_ = lean_ctor_get(v_a_2232_, 2);
v_currRecDepth_2536_ = lean_ctor_get(v_a_2232_, 3);
v_maxRecDepth_2537_ = lean_ctor_get(v_a_2232_, 4);
v_ref_2538_ = lean_ctor_get(v_a_2232_, 5);
v_currNamespace_2539_ = lean_ctor_get(v_a_2232_, 6);
v_openDecls_2540_ = lean_ctor_get(v_a_2232_, 7);
v_initHeartbeats_2541_ = lean_ctor_get(v_a_2232_, 8);
v_maxHeartbeats_2542_ = lean_ctor_get(v_a_2232_, 9);
v_quotContext_2543_ = lean_ctor_get(v_a_2232_, 10);
v_currMacroScope_2544_ = lean_ctor_get(v_a_2232_, 11);
v_diag_2545_ = lean_ctor_get_uint8(v_a_2232_, sizeof(void*)*14);
v_cancelTk_x3f_2546_ = lean_ctor_get(v_a_2232_, 12);
v_suppressElabErrors_2547_ = lean_ctor_get_uint8(v_a_2232_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2548_ = lean_ctor_get(v_a_2232_, 13);
v_ref_2549_ = l_Lean_replaceRef(v_p_2224_, v_ref_2538_);
lean_inc_ref(v_inheritedTraceOptions_2548_);
lean_inc(v_cancelTk_x3f_2546_);
lean_inc(v_currMacroScope_2544_);
lean_inc(v_quotContext_2543_);
lean_inc(v_maxHeartbeats_2542_);
lean_inc(v_initHeartbeats_2541_);
lean_inc(v_openDecls_2540_);
lean_inc(v_currNamespace_2539_);
lean_inc(v_maxRecDepth_2537_);
lean_inc(v_currRecDepth_2536_);
lean_inc_ref(v_options_2535_);
lean_inc_ref(v_fileMap_2534_);
lean_inc_ref(v_fileName_2533_);
v___x_2550_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2550_, 0, v_fileName_2533_);
lean_ctor_set(v___x_2550_, 1, v_fileMap_2534_);
lean_ctor_set(v___x_2550_, 2, v_options_2535_);
lean_ctor_set(v___x_2550_, 3, v_currRecDepth_2536_);
lean_ctor_set(v___x_2550_, 4, v_maxRecDepth_2537_);
lean_ctor_set(v___x_2550_, 5, v_ref_2549_);
lean_ctor_set(v___x_2550_, 6, v_currNamespace_2539_);
lean_ctor_set(v___x_2550_, 7, v_openDecls_2540_);
lean_ctor_set(v___x_2550_, 8, v_initHeartbeats_2541_);
lean_ctor_set(v___x_2550_, 9, v_maxHeartbeats_2542_);
lean_ctor_set(v___x_2550_, 10, v_quotContext_2543_);
lean_ctor_set(v___x_2550_, 11, v_currMacroScope_2544_);
lean_ctor_set(v___x_2550_, 12, v_cancelTk_x3f_2546_);
lean_ctor_set(v___x_2550_, 13, v_inheritedTraceOptions_2548_);
lean_ctor_set_uint8(v___x_2550_, sizeof(void*)*14, v_diag_2545_);
lean_ctor_set_uint8(v___x_2550_, sizeof(void*)*14 + 1, v_suppressElabErrors_2547_);
v___x_2551_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2223_, v___x_2550_, v_a_2233_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_dec_ref_known(v___x_2551_, 1);
if (lean_obj_tag(v_mod_x3f_2225_) == 1)
{
lean_object* v_val_2552_; lean_object* v___x_2553_; 
v_val_2552_ = lean_ctor_get(v_mod_x3f_2225_, 0);
lean_inc(v_val_2552_);
v___x_2553_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2552_, v___x_2550_, v_a_2233_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
switch(lean_obj_tag(v_a_2554_))
{
case 0:
{
lean_object* v_k_2572_; 
v_k_2572_ = lean_ctor_get(v_a_2554_, 0);
lean_inc(v_k_2572_);
lean_dec_ref_known(v_a_2554_, 1);
if (lean_obj_tag(v_k_2572_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2225_, 1);
lean_dec(v_term_2226_);
lean_dec(v_p_2224_);
lean_dec_ref(v_params_2223_);
v___y_2556_ = v_a_2228_;
v___y_2557_ = v_a_2229_;
v___y_2558_ = v_a_2230_;
v___y_2559_ = v_a_2231_;
v___y_2560_ = v___x_2550_;
v___y_2561_ = v_a_2233_;
goto v___jp_2555_;
}
else
{
v_kind_2460_ = v_k_2572_;
v___y_2461_ = v_a_2228_;
v___y_2462_ = v_a_2229_;
v___y_2463_ = v_a_2230_;
v___y_2464_ = v_a_2231_;
v___y_2465_ = v___x_2550_;
v___y_2466_ = v_a_2233_;
goto v___jp_2459_;
}
}
case 1:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_dec_ref_known(v_a_2554_, 0);
lean_dec_ref_known(v_mod_x3f_2225_, 1);
lean_dec(v_term_2226_);
lean_dec(v_p_2224_);
lean_dec_ref(v_params_2223_);
v___x_2573_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2574_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2573_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v___x_2550_, v_a_2233_);
lean_dec_ref_known(v___x_2550_, 14);
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
case 3:
{
v___y_2526_ = v_a_2228_;
v___y_2527_ = v_a_2229_;
v___y_2528_ = v_a_2230_;
v___y_2529_ = v_a_2231_;
v___y_2530_ = v___x_2550_;
v___y_2531_ = v_a_2233_;
goto v___jp_2525_;
}
case 5:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec_ref_known(v_a_2554_, 1);
lean_dec_ref_known(v_mod_x3f_2225_, 1);
lean_dec(v_term_2226_);
lean_dec(v_p_2224_);
lean_dec_ref(v_params_2223_);
v___x_2583_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2584_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2583_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v___x_2550_, v_a_2233_);
lean_dec_ref_known(v___x_2550_, 14);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
case 8:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref_known(v_a_2554_, 0);
lean_dec_ref_known(v_mod_x3f_2225_, 1);
lean_dec(v_term_2226_);
lean_dec(v_p_2224_);
lean_dec_ref(v_params_2223_);
v___x_2593_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2594_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2593_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v___x_2550_, v_a_2233_);
lean_dec_ref_known(v___x_2550_, 14);
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
default: 
{
lean_dec(v_a_2554_);
lean_dec_ref_known(v_mod_x3f_2225_, 1);
lean_dec(v_term_2226_);
lean_dec(v_p_2224_);
lean_dec_ref(v_params_2223_);
v___y_2556_ = v_a_2228_;
v___y_2557_ = v_a_2229_;
v___y_2558_ = v_a_2230_;
v___y_2559_ = v_a_2231_;
v___y_2560_ = v___x_2550_;
v___y_2561_ = v_a_2233_;
goto v___jp_2555_;
}
}
v___jp_2555_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
v___x_2562_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2563_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2562_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec_ref(v___y_2560_);
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
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
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec_ref_known(v_mod_x3f_2225_, 1);
lean_dec_ref_known(v___x_2550_, 14);
lean_dec(v_term_2226_);
lean_dec(v_p_2224_);
lean_dec_ref(v_params_2223_);
v_a_2603_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2553_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2553_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
else
{
v___y_2526_ = v_a_2228_;
v___y_2527_ = v_a_2229_;
v___y_2528_ = v_a_2230_;
v___y_2529_ = v_a_2231_;
v___y_2530_ = v___x_2550_;
v___y_2531_ = v_a_2233_;
goto v___jp_2525_;
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec_ref_known(v___x_2550_, 14);
lean_dec(v_term_2226_);
lean_dec(v_mod_x3f_2225_);
lean_dec(v_p_2224_);
lean_dec_ref(v_params_2223_);
v_a_2611_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2551_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2551_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
v___jp_2235_:
{
lean_object* v___x_2252_; 
lean_inc(v___y_2251_);
lean_inc(v___y_2249_);
lean_inc_ref(v___y_2248_);
v___x_2252_ = lean_apply_7(v___y_2247_, v___y_2237_, v___y_2240_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, lean_box(0));
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2262_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2262_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2262_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2257_ = l_Lean_PersistentArray_push___redArg(v___y_2242_, v_a_2253_);
v___x_2258_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2258_, 0, v___y_2236_);
lean_ctor_set(v___x_2258_, 1, v___y_2246_);
lean_ctor_set(v___x_2258_, 2, v___x_2257_);
lean_ctor_set(v___x_2258_, 3, v___y_2245_);
lean_ctor_set(v___x_2258_, 4, v___y_2241_);
lean_ctor_set(v___x_2258_, 5, v___y_2244_);
lean_ctor_set(v___x_2258_, 6, v___y_2243_);
lean_ctor_set(v___x_2258_, 7, v___y_2239_);
lean_ctor_set(v___x_2258_, 8, v___y_2238_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2258_);
v___x_2260_ = v___x_2255_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec_ref(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2236_);
v_a_2263_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2252_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2252_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
v___jp_2271_:
{
lean_object* v___x_2288_; 
v___x_2288_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2227_, v___y_2287_, v___y_2276_, v___y_2282_, v___y_2277_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_dec_ref_known(v___x_2288_, 1);
v___y_2236_ = v___y_2272_;
v___y_2237_ = v___y_2283_;
v___y_2238_ = v___y_2273_;
v___y_2239_ = v___y_2274_;
v___y_2240_ = v___y_2275_;
v___y_2241_ = v___y_2284_;
v___y_2242_ = v___y_2278_;
v___y_2243_ = v___y_2285_;
v___y_2244_ = v___y_2286_;
v___y_2245_ = v___y_2279_;
v___y_2246_ = v___y_2281_;
v___y_2247_ = v___y_2280_;
v___y_2248_ = v___y_2287_;
v___y_2249_ = v___y_2276_;
v___y_2250_ = v___y_2282_;
v___y_2251_ = v___y_2277_;
goto v___jp_2235_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec_ref(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
v___jp_2297_:
{
lean_object* v_config_2299_; lean_object* v_extensions_2300_; lean_object* v_extra_2301_; lean_object* v_extraInj_2302_; lean_object* v_extraFacts_2303_; lean_object* v_symPrios_2304_; lean_object* v_norm_2305_; lean_object* v_normProcs_2306_; lean_object* v_anchorRefs_x3f_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2316_; 
v_config_2299_ = lean_ctor_get(v_params_2223_, 0);
v_extensions_2300_ = lean_ctor_get(v_params_2223_, 1);
v_extra_2301_ = lean_ctor_get(v_params_2223_, 2);
v_extraInj_2302_ = lean_ctor_get(v_params_2223_, 3);
v_extraFacts_2303_ = lean_ctor_get(v_params_2223_, 4);
v_symPrios_2304_ = lean_ctor_get(v_params_2223_, 5);
v_norm_2305_ = lean_ctor_get(v_params_2223_, 6);
v_normProcs_2306_ = lean_ctor_get(v_params_2223_, 7);
v_anchorRefs_x3f_2307_ = lean_ctor_get(v_params_2223_, 8);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_params_2223_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2309_ = v_params_2223_;
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_anchorRefs_x3f_2307_);
lean_inc(v_normProcs_2306_);
lean_inc(v_norm_2305_);
lean_inc(v_symPrios_2304_);
lean_inc(v_extraFacts_2303_);
lean_inc(v_extraInj_2302_);
lean_inc(v_extra_2301_);
lean_inc(v_extensions_2300_);
lean_inc(v_config_2299_);
lean_dec(v_params_2223_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2303_, v___y_2298_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v___x_2311_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_config_2299_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_extensions_2300_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_extra_2301_);
lean_ctor_set(v_reuseFailAlloc_2315_, 3, v_extraInj_2302_);
lean_ctor_set(v_reuseFailAlloc_2315_, 4, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2315_, 5, v_symPrios_2304_);
lean_ctor_set(v_reuseFailAlloc_2315_, 6, v_norm_2305_);
lean_ctor_set(v_reuseFailAlloc_2315_, 7, v_normProcs_2306_);
lean_ctor_set(v_reuseFailAlloc_2315_, 8, v_anchorRefs_x3f_2307_);
v___x_2313_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
return v___x_2314_;
}
}
}
v___jp_2317_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2327_ = lean_array_get_size(v___y_2320_);
lean_dec_ref(v___y_2320_);
v___x_2328_ = lean_unsigned_to_nat(0u);
v___x_2329_ = lean_nat_dec_eq(v___x_2327_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec_ref(v___y_2318_);
lean_dec_ref(v_params_2223_);
v___x_2330_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2331_ = l_Lean_indentExpr(v___y_2319_);
v___x_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2332_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec_ref(v___y_2325_);
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
else
{
lean_dec_ref(v___y_2325_);
lean_dec_ref(v___y_2319_);
v___y_2298_ = v___y_2318_;
goto v___jp_2297_;
}
}
v___jp_2342_:
{
uint8_t v___x_2354_; 
v___x_2354_ = l_Lean_Expr_isForall(v___y_2345_);
if (v___x_2354_ == 0)
{
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2343_);
if (lean_obj_tag(v_mod_x3f_2225_) == 0)
{
v___y_2318_ = v___y_2344_;
v___y_2319_ = v___y_2345_;
v___y_2320_ = v___y_2346_;
v___y_2321_ = v___y_2348_;
v___y_2322_ = v___y_2349_;
v___y_2323_ = v___y_2350_;
v___y_2324_ = v___y_2351_;
v___y_2325_ = v___y_2352_;
v___y_2326_ = v___y_2353_;
goto v___jp_2317_;
}
else
{
lean_dec_ref_known(v_mod_x3f_2225_, 1);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v___y_2346_);
lean_dec_ref(v___y_2344_);
lean_dec_ref(v_params_2223_);
v___x_2355_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2356_ = l_Lean_indentExpr(v___y_2345_);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2357_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec_ref(v___y_2352_);
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
else
{
v___y_2318_ = v___y_2344_;
v___y_2319_ = v___y_2345_;
v___y_2320_ = v___y_2346_;
v___y_2321_ = v___y_2348_;
v___y_2322_ = v___y_2349_;
v___y_2323_ = v___y_2350_;
v___y_2324_ = v___y_2351_;
v___y_2325_ = v___y_2352_;
v___y_2326_ = v___y_2353_;
goto v___jp_2317_;
}
}
}
else
{
lean_object* v_extra_2367_; 
lean_dec_ref(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v_mod_x3f_2225_);
v_extra_2367_ = lean_ctor_get(v_params_2223_, 2);
lean_inc_ref(v_extra_2367_);
if (lean_obj_tag(v___y_2343_) == 2)
{
lean_object* v_config_2368_; lean_object* v_extensions_2369_; lean_object* v_extraInj_2370_; lean_object* v_extraFacts_2371_; lean_object* v_symPrios_2372_; lean_object* v_norm_2373_; lean_object* v_normProcs_2374_; lean_object* v_anchorRefs_x3f_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2430_; 
v_config_2368_ = lean_ctor_get(v_params_2223_, 0);
v_extensions_2369_ = lean_ctor_get(v_params_2223_, 1);
v_extraInj_2370_ = lean_ctor_get(v_params_2223_, 3);
v_extraFacts_2371_ = lean_ctor_get(v_params_2223_, 4);
v_symPrios_2372_ = lean_ctor_get(v_params_2223_, 5);
v_norm_2373_ = lean_ctor_get(v_params_2223_, 6);
v_normProcs_2374_ = lean_ctor_get(v_params_2223_, 7);
v_anchorRefs_x3f_2375_ = lean_ctor_get(v_params_2223_, 8);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_params_2223_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; 
v_unused_2431_ = lean_ctor_get(v_params_2223_, 2);
lean_dec(v_unused_2431_);
v___x_2377_ = v_params_2223_;
v_isShared_2378_ = v_isSharedCheck_2430_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_anchorRefs_x3f_2375_);
lean_inc(v_normProcs_2374_);
lean_inc(v_norm_2373_);
lean_inc(v_symPrios_2372_);
lean_inc(v_extraFacts_2371_);
lean_inc(v_extraInj_2370_);
lean_inc(v_extensions_2369_);
lean_inc(v_config_2368_);
lean_dec(v_params_2223_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2430_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v_size_2379_; uint8_t v_gen_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2429_; 
v_size_2379_ = lean_ctor_get(v_extra_2367_, 2);
v_gen_2380_ = lean_ctor_get_uint8(v___y_2343_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___y_2343_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2382_ = v___y_2343_;
v_isShared_2383_ = v_isSharedCheck_2429_;
goto v_resetjp_2381_;
}
else
{
lean_dec(v___y_2343_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2429_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; 
v___x_2384_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2227_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v___x_2386_; 
lean_dec_ref_known(v___x_2384_, 1);
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 0);
v___x_2386_ = v___x_2382_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 0, v_gen_2380_);
v___x_2386_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2387_; 
lean_inc_ref(v___y_2347_);
lean_inc(v___y_2353_);
lean_inc_ref(v___y_2352_);
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
lean_inc(v_size_2379_);
v___x_2387_ = lean_apply_7(v___y_2347_, v___x_2386_, v_size_2379_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, lean_box(0));
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2389_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2389_, 0, v_gen_2380_);
lean_inc(v___y_2353_);
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
lean_inc(v_size_2379_);
v___x_2390_ = lean_apply_7(v___y_2347_, v___x_2389_, v_size_2379_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, lean_box(0));
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2403_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2403_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2403_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2398_; 
v___x_2395_ = l_Lean_PersistentArray_push___redArg(v_extra_2367_, v_a_2388_);
v___x_2396_ = l_Lean_PersistentArray_push___redArg(v___x_2395_, v_a_2391_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 2, v___x_2396_);
v___x_2398_ = v___x_2377_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_config_2368_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_extensions_2369_);
lean_ctor_set(v_reuseFailAlloc_2402_, 2, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2402_, 3, v_extraInj_2370_);
lean_ctor_set(v_reuseFailAlloc_2402_, 4, v_extraFacts_2371_);
lean_ctor_set(v_reuseFailAlloc_2402_, 5, v_symPrios_2372_);
lean_ctor_set(v_reuseFailAlloc_2402_, 6, v_norm_2373_);
lean_ctor_set(v_reuseFailAlloc_2402_, 7, v_normProcs_2374_);
lean_ctor_set(v_reuseFailAlloc_2402_, 8, v_anchorRefs_x3f_2375_);
v___x_2398_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2400_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2398_);
v___x_2400_ = v___x_2393_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_a_2388_);
lean_del_object(v___x_2377_);
lean_dec(v_anchorRefs_x3f_2375_);
lean_dec_ref(v_normProcs_2374_);
lean_dec_ref(v_norm_2373_);
lean_dec_ref(v_symPrios_2372_);
lean_dec_ref(v_extraFacts_2371_);
lean_dec_ref(v_extraInj_2370_);
lean_dec_ref(v_extensions_2369_);
lean_dec_ref(v_config_2368_);
lean_dec_ref(v_extra_2367_);
v_a_2404_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2390_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2390_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_del_object(v___x_2377_);
lean_dec(v_anchorRefs_x3f_2375_);
lean_dec_ref(v_normProcs_2374_);
lean_dec_ref(v_norm_2373_);
lean_dec_ref(v_symPrios_2372_);
lean_dec_ref(v_extraFacts_2371_);
lean_dec_ref(v_extraInj_2370_);
lean_dec_ref(v_extensions_2369_);
lean_dec_ref(v_config_2368_);
lean_dec_ref(v_extra_2367_);
lean_dec_ref(v___y_2352_);
lean_dec_ref(v___y_2347_);
v_a_2412_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2387_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2387_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_del_object(v___x_2382_);
lean_del_object(v___x_2377_);
lean_dec(v_anchorRefs_x3f_2375_);
lean_dec_ref(v_normProcs_2374_);
lean_dec_ref(v_norm_2373_);
lean_dec_ref(v_symPrios_2372_);
lean_dec_ref(v_extraFacts_2371_);
lean_dec_ref(v_extraInj_2370_);
lean_dec_ref(v_extensions_2369_);
lean_dec_ref(v_config_2368_);
lean_dec_ref(v_extra_2367_);
lean_dec_ref(v___y_2352_);
lean_dec_ref(v___y_2347_);
v_a_2421_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2384_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2384_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
}
else
{
switch(lean_obj_tag(v___y_2343_))
{
case 0:
{
lean_object* v_config_2432_; lean_object* v_extensions_2433_; lean_object* v_extraInj_2434_; lean_object* v_extraFacts_2435_; lean_object* v_symPrios_2436_; lean_object* v_norm_2437_; lean_object* v_normProcs_2438_; lean_object* v_anchorRefs_x3f_2439_; lean_object* v_size_2440_; 
v_config_2432_ = lean_ctor_get(v_params_2223_, 0);
lean_inc_ref(v_config_2432_);
v_extensions_2433_ = lean_ctor_get(v_params_2223_, 1);
lean_inc_ref(v_extensions_2433_);
v_extraInj_2434_ = lean_ctor_get(v_params_2223_, 3);
lean_inc_ref(v_extraInj_2434_);
v_extraFacts_2435_ = lean_ctor_get(v_params_2223_, 4);
lean_inc_ref(v_extraFacts_2435_);
v_symPrios_2436_ = lean_ctor_get(v_params_2223_, 5);
lean_inc_ref(v_symPrios_2436_);
v_norm_2437_ = lean_ctor_get(v_params_2223_, 6);
lean_inc_ref(v_norm_2437_);
v_normProcs_2438_ = lean_ctor_get(v_params_2223_, 7);
lean_inc_ref(v_normProcs_2438_);
v_anchorRefs_x3f_2439_ = lean_ctor_get(v_params_2223_, 8);
lean_inc(v_anchorRefs_x3f_2439_);
lean_dec_ref(v_params_2223_);
v_size_2440_ = lean_ctor_get(v_extra_2367_, 2);
lean_inc(v_size_2440_);
v___y_2272_ = v_config_2432_;
v___y_2273_ = v_anchorRefs_x3f_2439_;
v___y_2274_ = v_normProcs_2438_;
v___y_2275_ = v_size_2440_;
v___y_2276_ = v___y_2351_;
v___y_2277_ = v___y_2353_;
v___y_2278_ = v_extra_2367_;
v___y_2279_ = v_extraInj_2434_;
v___y_2280_ = v___y_2347_;
v___y_2281_ = v_extensions_2433_;
v___y_2282_ = v___y_2352_;
v___y_2283_ = v___y_2343_;
v___y_2284_ = v_extraFacts_2435_;
v___y_2285_ = v_norm_2437_;
v___y_2286_ = v_symPrios_2436_;
v___y_2287_ = v___y_2350_;
goto v___jp_2271_;
}
case 1:
{
lean_object* v_config_2441_; lean_object* v_extensions_2442_; lean_object* v_extraInj_2443_; lean_object* v_extraFacts_2444_; lean_object* v_symPrios_2445_; lean_object* v_norm_2446_; lean_object* v_normProcs_2447_; lean_object* v_anchorRefs_x3f_2448_; lean_object* v_size_2449_; 
v_config_2441_ = lean_ctor_get(v_params_2223_, 0);
lean_inc_ref(v_config_2441_);
v_extensions_2442_ = lean_ctor_get(v_params_2223_, 1);
lean_inc_ref(v_extensions_2442_);
v_extraInj_2443_ = lean_ctor_get(v_params_2223_, 3);
lean_inc_ref(v_extraInj_2443_);
v_extraFacts_2444_ = lean_ctor_get(v_params_2223_, 4);
lean_inc_ref(v_extraFacts_2444_);
v_symPrios_2445_ = lean_ctor_get(v_params_2223_, 5);
lean_inc_ref(v_symPrios_2445_);
v_norm_2446_ = lean_ctor_get(v_params_2223_, 6);
lean_inc_ref(v_norm_2446_);
v_normProcs_2447_ = lean_ctor_get(v_params_2223_, 7);
lean_inc_ref(v_normProcs_2447_);
v_anchorRefs_x3f_2448_ = lean_ctor_get(v_params_2223_, 8);
lean_inc(v_anchorRefs_x3f_2448_);
lean_dec_ref(v_params_2223_);
v_size_2449_ = lean_ctor_get(v_extra_2367_, 2);
lean_inc(v_size_2449_);
v___y_2272_ = v_config_2441_;
v___y_2273_ = v_anchorRefs_x3f_2448_;
v___y_2274_ = v_normProcs_2447_;
v___y_2275_ = v_size_2449_;
v___y_2276_ = v___y_2351_;
v___y_2277_ = v___y_2353_;
v___y_2278_ = v_extra_2367_;
v___y_2279_ = v_extraInj_2443_;
v___y_2280_ = v___y_2347_;
v___y_2281_ = v_extensions_2442_;
v___y_2282_ = v___y_2352_;
v___y_2283_ = v___y_2343_;
v___y_2284_ = v_extraFacts_2444_;
v___y_2285_ = v_norm_2446_;
v___y_2286_ = v_symPrios_2445_;
v___y_2287_ = v___y_2350_;
goto v___jp_2271_;
}
default: 
{
lean_object* v_config_2450_; lean_object* v_extensions_2451_; lean_object* v_extraInj_2452_; lean_object* v_extraFacts_2453_; lean_object* v_symPrios_2454_; lean_object* v_norm_2455_; lean_object* v_normProcs_2456_; lean_object* v_anchorRefs_x3f_2457_; lean_object* v_size_2458_; 
v_config_2450_ = lean_ctor_get(v_params_2223_, 0);
lean_inc_ref(v_config_2450_);
v_extensions_2451_ = lean_ctor_get(v_params_2223_, 1);
lean_inc_ref(v_extensions_2451_);
v_extraInj_2452_ = lean_ctor_get(v_params_2223_, 3);
lean_inc_ref(v_extraInj_2452_);
v_extraFacts_2453_ = lean_ctor_get(v_params_2223_, 4);
lean_inc_ref(v_extraFacts_2453_);
v_symPrios_2454_ = lean_ctor_get(v_params_2223_, 5);
lean_inc_ref(v_symPrios_2454_);
v_norm_2455_ = lean_ctor_get(v_params_2223_, 6);
lean_inc_ref(v_norm_2455_);
v_normProcs_2456_ = lean_ctor_get(v_params_2223_, 7);
lean_inc_ref(v_normProcs_2456_);
v_anchorRefs_x3f_2457_ = lean_ctor_get(v_params_2223_, 8);
lean_inc(v_anchorRefs_x3f_2457_);
lean_dec_ref(v_params_2223_);
v_size_2458_ = lean_ctor_get(v_extra_2367_, 2);
lean_inc(v_size_2458_);
v___y_2236_ = v_config_2450_;
v___y_2237_ = v___y_2343_;
v___y_2238_ = v_anchorRefs_x3f_2457_;
v___y_2239_ = v_normProcs_2456_;
v___y_2240_ = v_size_2458_;
v___y_2241_ = v_extraFacts_2453_;
v___y_2242_ = v_extra_2367_;
v___y_2243_ = v_norm_2455_;
v___y_2244_ = v_symPrios_2454_;
v___y_2245_ = v_extraInj_2452_;
v___y_2246_ = v_extensions_2451_;
v___y_2247_ = v___y_2347_;
v___y_2248_ = v___y_2350_;
v___y_2249_ = v___y_2351_;
v___y_2250_ = v___y_2352_;
v___y_2251_ = v___y_2353_;
goto v___jp_2235_;
}
}
}
}
}
v___jp_2459_:
{
lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___f_2470_; lean_object* v___x_2471_; 
v___x_2467_ = lean_box(0);
v___x_2468_ = 1;
v___x_2469_ = lean_box(v___x_2468_);
lean_inc(v_p_2224_);
v___f_2470_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2470_, 0, v_p_2224_);
lean_closure_set(v___f_2470_, 1, v_term_2226_);
lean_closure_set(v___f_2470_, 2, v___x_2467_);
lean_closure_set(v___f_2470_, 3, v___x_2469_);
v___x_2471_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2470_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2516_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2516_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2516_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
if (lean_obj_tag(v_a_2472_) == 1)
{
lean_object* v_val_2476_; lean_object* v_fst_2477_; lean_object* v_snd_2478_; lean_object* v___x_2479_; 
lean_del_object(v___x_2474_);
v_val_2476_ = lean_ctor_get(v_a_2472_, 0);
lean_inc(v_val_2476_);
lean_dec_ref_known(v_a_2472_, 1);
v_fst_2477_ = lean_ctor_get(v_val_2476_, 0);
lean_inc(v_fst_2477_);
v_snd_2478_ = lean_ctor_get(v_val_2476_, 1);
lean_inc_n(v_snd_2478_, 2);
lean_dec(v_val_2476_);
lean_inc(v___y_2466_);
lean_inc_ref(v___y_2465_);
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
v___x_2479_ = lean_infer_type(v_snd_2478_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2481_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc_n(v_a_2480_, 2);
lean_dec_ref_known(v___x_2479_, 1);
v___x_2481_ = l_Lean_Meta_isProp(v_a_2480_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___f_2485_; uint8_t v___x_2486_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v___x_2483_ = lean_box(v___x_2468_);
v___x_2484_ = lean_box(v_minIndexable_2227_);
lean_inc(v_snd_2478_);
lean_inc(v_fst_2477_);
lean_inc_ref(v_params_2223_);
v___f_2485_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2485_, 0, v_params_2223_);
lean_closure_set(v___f_2485_, 1, v_p_2224_);
lean_closure_set(v___f_2485_, 2, v_fst_2477_);
lean_closure_set(v___f_2485_, 3, v_snd_2478_);
lean_closure_set(v___f_2485_, 4, v___x_2483_);
lean_closure_set(v___f_2485_, 5, v___x_2484_);
v___x_2486_ = lean_unbox(v_a_2482_);
lean_dec(v_a_2482_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec_ref(v___f_2485_);
lean_dec(v_a_2480_);
lean_dec(v_snd_2478_);
lean_dec(v_fst_2477_);
lean_dec(v_kind_2460_);
lean_dec(v_mod_x3f_2225_);
lean_dec_ref(v_params_2223_);
v___x_2487_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2488_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2487_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec_ref(v___y_2465_);
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
else
{
v___y_2343_ = v_kind_2460_;
v___y_2344_ = v_snd_2478_;
v___y_2345_ = v_a_2480_;
v___y_2346_ = v_fst_2477_;
v___y_2347_ = v___f_2485_;
v___y_2348_ = v___y_2461_;
v___y_2349_ = v___y_2462_;
v___y_2350_ = v___y_2463_;
v___y_2351_ = v___y_2464_;
v___y_2352_ = v___y_2465_;
v___y_2353_ = v___y_2466_;
goto v___jp_2342_;
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_a_2480_);
lean_dec(v_snd_2478_);
lean_dec(v_fst_2477_);
lean_dec_ref(v___y_2465_);
lean_dec(v_kind_2460_);
lean_dec(v_mod_x3f_2225_);
lean_dec(v_p_2224_);
lean_dec_ref(v_params_2223_);
v_a_2497_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2481_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2481_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_snd_2478_);
lean_dec(v_fst_2477_);
lean_dec_ref(v___y_2465_);
lean_dec(v_kind_2460_);
lean_dec(v_mod_x3f_2225_);
lean_dec(v_p_2224_);
lean_dec_ref(v_params_2223_);
v_a_2505_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2479_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2479_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v___x_2514_; 
lean_dec(v_a_2472_);
lean_dec_ref(v___y_2465_);
lean_dec(v_kind_2460_);
lean_dec(v_mod_x3f_2225_);
lean_dec(v_p_2224_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v_params_2223_);
v___x_2514_ = v___x_2474_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_params_2223_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v___y_2465_);
lean_dec(v_kind_2460_);
lean_dec(v_mod_x3f_2225_);
lean_dec(v_p_2224_);
lean_dec_ref(v_params_2223_);
v_a_2517_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2471_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2471_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
v___jp_2525_:
{
lean_object* v___x_2532_; 
v___x_2532_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_kind_2460_ = v___x_2532_;
v___y_2461_ = v___y_2526_;
v___y_2462_ = v___y_2527_;
v___y_2463_ = v___y_2528_;
v___y_2464_ = v___y_2529_;
v___y_2465_ = v___y_2530_;
v___y_2466_ = v___y_2531_;
goto v___jp_2459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2619_, lean_object* v_p_2620_, lean_object* v_mod_x3f_2621_, lean_object* v_term_2622_, lean_object* v_minIndexable_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
uint8_t v_minIndexable_boxed_2631_; lean_object* v_res_2632_; 
v_minIndexable_boxed_2631_ = lean_unbox(v_minIndexable_2623_);
v_res_2632_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2619_, v_p_2620_, v_mod_x3f_2621_, v_term_2622_, v_minIndexable_boxed_2631_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object* v_00_u03b1_2633_, lean_object* v_msg_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v_00_u03b1_2643_, lean_object* v_msg_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v_00_u03b1_2643_, v_msg_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object* v_msgData_2653_, lean_object* v_macroStack_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2653_, v_macroStack_2654_, v___y_2659_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object* v_msgData_2663_, lean_object* v_macroStack_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(v_msgData_2663_, v_macroStack_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2673_, lean_object* v_val_2674_, lean_object* v_____r_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v___x_2683_; lean_object* v_ext_2684_; lean_object* v_toEnvExtension_2685_; lean_object* v_env_2686_; lean_object* v_config_2687_; lean_object* v_extensions_2688_; lean_object* v_extra_2689_; lean_object* v_extraInj_2690_; lean_object* v_extraFacts_2691_; lean_object* v_symPrios_2692_; lean_object* v_norm_2693_; lean_object* v_normProcs_2694_; lean_object* v_anchorRefs_x3f_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2708_; 
v___x_2683_ = lean_st_ref_get(v___y_2681_);
v_ext_2684_ = lean_ctor_get(v_val_2674_, 1);
v_toEnvExtension_2685_ = lean_ctor_get(v_ext_2684_, 0);
v_env_2686_ = lean_ctor_get(v___x_2683_, 0);
lean_inc_ref(v_env_2686_);
lean_dec(v___x_2683_);
v_config_2687_ = lean_ctor_get(v_params_2673_, 0);
v_extensions_2688_ = lean_ctor_get(v_params_2673_, 1);
v_extra_2689_ = lean_ctor_get(v_params_2673_, 2);
v_extraInj_2690_ = lean_ctor_get(v_params_2673_, 3);
v_extraFacts_2691_ = lean_ctor_get(v_params_2673_, 4);
v_symPrios_2692_ = lean_ctor_get(v_params_2673_, 5);
v_norm_2693_ = lean_ctor_get(v_params_2673_, 6);
v_normProcs_2694_ = lean_ctor_get(v_params_2673_, 7);
v_anchorRefs_x3f_2695_ = lean_ctor_get(v_params_2673_, 8);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_params_2673_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2697_ = v_params_2673_;
v_isShared_2698_ = v_isSharedCheck_2708_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_anchorRefs_x3f_2695_);
lean_inc(v_normProcs_2694_);
lean_inc(v_norm_2693_);
lean_inc(v_symPrios_2692_);
lean_inc(v_extraFacts_2691_);
lean_inc(v_extraInj_2690_);
lean_inc(v_extra_2689_);
lean_inc(v_extensions_2688_);
lean_inc(v_config_2687_);
lean_dec(v_params_2673_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2708_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v_asyncMode_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v_asyncMode_2699_ = lean_ctor_get(v_toEnvExtension_2685_, 2);
v___x_2700_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2701_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2700_, v_val_2674_, v_env_2686_, v_asyncMode_2699_);
v___x_2702_ = lean_array_push(v_extensions_2688_, v___x_2701_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___x_2702_);
v___x_2704_ = v___x_2697_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_config_2687_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_extra_2689_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_extraInj_2690_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_extraFacts_2691_);
lean_ctor_set(v_reuseFailAlloc_2707_, 5, v_symPrios_2692_);
lean_ctor_set(v_reuseFailAlloc_2707_, 6, v_norm_2693_);
lean_ctor_set(v_reuseFailAlloc_2707_, 7, v_normProcs_2694_);
lean_ctor_set(v_reuseFailAlloc_2707_, 8, v_anchorRefs_x3f_2695_);
v___x_2704_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
return v___x_2706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2709_, lean_object* v_val_2710_, lean_object* v_____r_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2709_, v_val_2710_, v_____r_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec_ref(v_val_2710_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2720_, lean_object* v_id_2721_, uint8_t v_minIndexable_2722_, lean_object* v_as_x27_2723_, lean_object* v_b_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
if (lean_obj_tag(v_as_x27_2723_) == 0)
{
lean_object* v___x_2730_; 
lean_dec(v_id_2721_);
v___x_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_b_2724_);
return v___x_2730_;
}
else
{
lean_object* v_head_2731_; lean_object* v_tail_2732_; lean_object* v_fileName_2733_; lean_object* v_fileMap_2734_; lean_object* v_options_2735_; lean_object* v_currRecDepth_2736_; lean_object* v_maxRecDepth_2737_; lean_object* v_ref_2738_; lean_object* v_currNamespace_2739_; lean_object* v_openDecls_2740_; lean_object* v_initHeartbeats_2741_; lean_object* v_maxHeartbeats_2742_; lean_object* v_quotContext_2743_; lean_object* v_currMacroScope_2744_; uint8_t v_diag_2745_; lean_object* v_cancelTk_x3f_2746_; uint8_t v_suppressElabErrors_2747_; lean_object* v_inheritedTraceOptions_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v_ref_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v_head_2731_ = lean_ctor_get(v_as_x27_2723_, 0);
v_tail_2732_ = lean_ctor_get(v_as_x27_2723_, 1);
v_fileName_2733_ = lean_ctor_get(v___y_2727_, 0);
v_fileMap_2734_ = lean_ctor_get(v___y_2727_, 1);
v_options_2735_ = lean_ctor_get(v___y_2727_, 2);
v_currRecDepth_2736_ = lean_ctor_get(v___y_2727_, 3);
v_maxRecDepth_2737_ = lean_ctor_get(v___y_2727_, 4);
v_ref_2738_ = lean_ctor_get(v___y_2727_, 5);
v_currNamespace_2739_ = lean_ctor_get(v___y_2727_, 6);
v_openDecls_2740_ = lean_ctor_get(v___y_2727_, 7);
v_initHeartbeats_2741_ = lean_ctor_get(v___y_2727_, 8);
v_maxHeartbeats_2742_ = lean_ctor_get(v___y_2727_, 9);
v_quotContext_2743_ = lean_ctor_get(v___y_2727_, 10);
v_currMacroScope_2744_ = lean_ctor_get(v___y_2727_, 11);
v_diag_2745_ = lean_ctor_get_uint8(v___y_2727_, sizeof(void*)*14);
v_cancelTk_x3f_2746_ = lean_ctor_get(v___y_2727_, 12);
v_suppressElabErrors_2747_ = lean_ctor_get_uint8(v___y_2727_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2748_ = lean_ctor_get(v___y_2727_, 13);
v___x_2749_ = 0;
v___x_2750_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_2751_ = l_Lean_replaceRef(v_p_2720_, v_ref_2738_);
lean_inc_ref(v_inheritedTraceOptions_2748_);
lean_inc(v_cancelTk_x3f_2746_);
lean_inc(v_currMacroScope_2744_);
lean_inc(v_quotContext_2743_);
lean_inc(v_maxHeartbeats_2742_);
lean_inc(v_initHeartbeats_2741_);
lean_inc(v_openDecls_2740_);
lean_inc(v_currNamespace_2739_);
lean_inc(v_maxRecDepth_2737_);
lean_inc(v_currRecDepth_2736_);
lean_inc_ref(v_options_2735_);
lean_inc_ref(v_fileMap_2734_);
lean_inc_ref(v_fileName_2733_);
v___x_2752_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2752_, 0, v_fileName_2733_);
lean_ctor_set(v___x_2752_, 1, v_fileMap_2734_);
lean_ctor_set(v___x_2752_, 2, v_options_2735_);
lean_ctor_set(v___x_2752_, 3, v_currRecDepth_2736_);
lean_ctor_set(v___x_2752_, 4, v_maxRecDepth_2737_);
lean_ctor_set(v___x_2752_, 5, v_ref_2751_);
lean_ctor_set(v___x_2752_, 6, v_currNamespace_2739_);
lean_ctor_set(v___x_2752_, 7, v_openDecls_2740_);
lean_ctor_set(v___x_2752_, 8, v_initHeartbeats_2741_);
lean_ctor_set(v___x_2752_, 9, v_maxHeartbeats_2742_);
lean_ctor_set(v___x_2752_, 10, v_quotContext_2743_);
lean_ctor_set(v___x_2752_, 11, v_currMacroScope_2744_);
lean_ctor_set(v___x_2752_, 12, v_cancelTk_x3f_2746_);
lean_ctor_set(v___x_2752_, 13, v_inheritedTraceOptions_2748_);
lean_ctor_set_uint8(v___x_2752_, sizeof(void*)*14, v_diag_2745_);
lean_ctor_set_uint8(v___x_2752_, sizeof(void*)*14 + 1, v_suppressElabErrors_2747_);
lean_inc(v_head_2731_);
lean_inc(v_id_2721_);
v___x_2753_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2724_, v_id_2721_, v_head_2731_, v___x_2750_, v_minIndexable_2722_, v___x_2749_, v___x_2749_, v___y_2725_, v___y_2726_, v___x_2752_, v___y_2728_);
lean_dec_ref_known(v___x_2752_, 14);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v___x_2753_, 1);
v_as_x27_2723_ = v_tail_2732_;
v_b_2724_ = v_a_2754_;
goto _start;
}
else
{
lean_dec(v_id_2721_);
return v___x_2753_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_2756_, lean_object* v_id_2757_, lean_object* v_minIndexable_2758_, lean_object* v_as_x27_2759_, lean_object* v_b_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
uint8_t v_minIndexable_boxed_2766_; lean_object* v_res_2767_; 
v_minIndexable_boxed_2766_ = lean_unbox(v_minIndexable_2758_);
v_res_2767_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2756_, v_id_2757_, v_minIndexable_boxed_2766_, v_as_x27_2759_, v_b_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v_as_x27_2759_);
lean_dec(v_p_2756_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
if (lean_obj_tag(v_a_2769_) == 0)
{
lean_object* v___x_2771_; 
v___x_2771_ = l_List_reverse___redArg(v_a_2770_);
return v___x_2771_;
}
else
{
lean_object* v_head_2772_; lean_object* v_tail_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2784_; 
v_head_2772_ = lean_ctor_get(v_a_2769_, 0);
v_tail_2773_ = lean_ctor_get(v_a_2769_, 1);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_a_2769_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2775_ = v_a_2769_;
v_isShared_2776_ = v_isSharedCheck_2784_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_tail_2773_);
lean_inc(v_head_2772_);
lean_dec(v_a_2769_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2784_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v_kind_2777_; uint8_t v___x_2778_; 
v_kind_2777_ = lean_ctor_get(v_head_2772_, 6);
v___x_2778_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_2777_, v_k_2768_);
if (v___x_2778_ == 0)
{
lean_del_object(v___x_2775_);
lean_dec(v_head_2772_);
v_a_2769_ = v_tail_2773_;
goto _start;
}
else
{
lean_object* v___x_2781_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 1, v_a_2770_);
v___x_2781_ = v___x_2775_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_head_2772_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_a_2770_);
v___x_2781_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
v_a_2769_ = v_tail_2773_;
v_a_2770_ = v___x_2781_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_2785_, v_a_2786_, v_a_2787_);
lean_dec(v_k_2785_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_2789_, lean_object* v_msg_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_fileName_2798_; lean_object* v_fileMap_2799_; lean_object* v_options_2800_; lean_object* v_currRecDepth_2801_; lean_object* v_maxRecDepth_2802_; lean_object* v_ref_2803_; lean_object* v_currNamespace_2804_; lean_object* v_openDecls_2805_; lean_object* v_initHeartbeats_2806_; lean_object* v_maxHeartbeats_2807_; lean_object* v_quotContext_2808_; lean_object* v_currMacroScope_2809_; uint8_t v_diag_2810_; lean_object* v_cancelTk_x3f_2811_; uint8_t v_suppressElabErrors_2812_; lean_object* v_inheritedTraceOptions_2813_; lean_object* v_ref_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_fileName_2798_ = lean_ctor_get(v___y_2795_, 0);
v_fileMap_2799_ = lean_ctor_get(v___y_2795_, 1);
v_options_2800_ = lean_ctor_get(v___y_2795_, 2);
v_currRecDepth_2801_ = lean_ctor_get(v___y_2795_, 3);
v_maxRecDepth_2802_ = lean_ctor_get(v___y_2795_, 4);
v_ref_2803_ = lean_ctor_get(v___y_2795_, 5);
v_currNamespace_2804_ = lean_ctor_get(v___y_2795_, 6);
v_openDecls_2805_ = lean_ctor_get(v___y_2795_, 7);
v_initHeartbeats_2806_ = lean_ctor_get(v___y_2795_, 8);
v_maxHeartbeats_2807_ = lean_ctor_get(v___y_2795_, 9);
v_quotContext_2808_ = lean_ctor_get(v___y_2795_, 10);
v_currMacroScope_2809_ = lean_ctor_get(v___y_2795_, 11);
v_diag_2810_ = lean_ctor_get_uint8(v___y_2795_, sizeof(void*)*14);
v_cancelTk_x3f_2811_ = lean_ctor_get(v___y_2795_, 12);
v_suppressElabErrors_2812_ = lean_ctor_get_uint8(v___y_2795_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2813_ = lean_ctor_get(v___y_2795_, 13);
v_ref_2814_ = l_Lean_replaceRef(v_ref_2789_, v_ref_2803_);
lean_inc_ref(v_inheritedTraceOptions_2813_);
lean_inc(v_cancelTk_x3f_2811_);
lean_inc(v_currMacroScope_2809_);
lean_inc(v_quotContext_2808_);
lean_inc(v_maxHeartbeats_2807_);
lean_inc(v_initHeartbeats_2806_);
lean_inc(v_openDecls_2805_);
lean_inc(v_currNamespace_2804_);
lean_inc(v_maxRecDepth_2802_);
lean_inc(v_currRecDepth_2801_);
lean_inc_ref(v_options_2800_);
lean_inc_ref(v_fileMap_2799_);
lean_inc_ref(v_fileName_2798_);
v___x_2815_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2815_, 0, v_fileName_2798_);
lean_ctor_set(v___x_2815_, 1, v_fileMap_2799_);
lean_ctor_set(v___x_2815_, 2, v_options_2800_);
lean_ctor_set(v___x_2815_, 3, v_currRecDepth_2801_);
lean_ctor_set(v___x_2815_, 4, v_maxRecDepth_2802_);
lean_ctor_set(v___x_2815_, 5, v_ref_2814_);
lean_ctor_set(v___x_2815_, 6, v_currNamespace_2804_);
lean_ctor_set(v___x_2815_, 7, v_openDecls_2805_);
lean_ctor_set(v___x_2815_, 8, v_initHeartbeats_2806_);
lean_ctor_set(v___x_2815_, 9, v_maxHeartbeats_2807_);
lean_ctor_set(v___x_2815_, 10, v_quotContext_2808_);
lean_ctor_set(v___x_2815_, 11, v_currMacroScope_2809_);
lean_ctor_set(v___x_2815_, 12, v_cancelTk_x3f_2811_);
lean_ctor_set(v___x_2815_, 13, v_inheritedTraceOptions_2813_);
lean_ctor_set_uint8(v___x_2815_, sizeof(void*)*14, v_diag_2810_);
lean_ctor_set_uint8(v___x_2815_, sizeof(void*)*14 + 1, v_suppressElabErrors_2812_);
v___x_2816_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___x_2815_, v___y_2796_);
lean_dec_ref_known(v___x_2815_, 14);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_2817_, lean_object* v_msg_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_2817_, v_msg_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v_ref_2817_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_2827_, lean_object* v_id_2828_, uint8_t v_minIndexable_2829_, lean_object* v_as_x27_2830_, lean_object* v_b_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
if (lean_obj_tag(v_as_x27_2830_) == 0)
{
lean_object* v___x_2837_; 
lean_dec(v_id_2828_);
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v_b_2831_);
return v___x_2837_;
}
else
{
lean_object* v_head_2838_; lean_object* v_tail_2839_; lean_object* v_fileName_2840_; lean_object* v_fileMap_2841_; lean_object* v_options_2842_; lean_object* v_currRecDepth_2843_; lean_object* v_maxRecDepth_2844_; lean_object* v_ref_2845_; lean_object* v_currNamespace_2846_; lean_object* v_openDecls_2847_; lean_object* v_initHeartbeats_2848_; lean_object* v_maxHeartbeats_2849_; lean_object* v_quotContext_2850_; lean_object* v_currMacroScope_2851_; uint8_t v_diag_2852_; lean_object* v_cancelTk_x3f_2853_; uint8_t v_suppressElabErrors_2854_; lean_object* v_inheritedTraceOptions_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; lean_object* v_ref_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v_head_2838_ = lean_ctor_get(v_as_x27_2830_, 0);
v_tail_2839_ = lean_ctor_get(v_as_x27_2830_, 1);
v_fileName_2840_ = lean_ctor_get(v___y_2834_, 0);
v_fileMap_2841_ = lean_ctor_get(v___y_2834_, 1);
v_options_2842_ = lean_ctor_get(v___y_2834_, 2);
v_currRecDepth_2843_ = lean_ctor_get(v___y_2834_, 3);
v_maxRecDepth_2844_ = lean_ctor_get(v___y_2834_, 4);
v_ref_2845_ = lean_ctor_get(v___y_2834_, 5);
v_currNamespace_2846_ = lean_ctor_get(v___y_2834_, 6);
v_openDecls_2847_ = lean_ctor_get(v___y_2834_, 7);
v_initHeartbeats_2848_ = lean_ctor_get(v___y_2834_, 8);
v_maxHeartbeats_2849_ = lean_ctor_get(v___y_2834_, 9);
v_quotContext_2850_ = lean_ctor_get(v___y_2834_, 10);
v_currMacroScope_2851_ = lean_ctor_get(v___y_2834_, 11);
v_diag_2852_ = lean_ctor_get_uint8(v___y_2834_, sizeof(void*)*14);
v_cancelTk_x3f_2853_ = lean_ctor_get(v___y_2834_, 12);
v_suppressElabErrors_2854_ = lean_ctor_get_uint8(v___y_2834_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2855_ = lean_ctor_get(v___y_2834_, 13);
v___x_2856_ = 0;
v___x_2857_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2858_ = 1;
v_ref_2859_ = l_Lean_replaceRef(v_p_2827_, v_ref_2845_);
lean_inc_ref(v_inheritedTraceOptions_2855_);
lean_inc(v_cancelTk_x3f_2853_);
lean_inc(v_currMacroScope_2851_);
lean_inc(v_quotContext_2850_);
lean_inc(v_maxHeartbeats_2849_);
lean_inc(v_initHeartbeats_2848_);
lean_inc(v_openDecls_2847_);
lean_inc(v_currNamespace_2846_);
lean_inc(v_maxRecDepth_2844_);
lean_inc(v_currRecDepth_2843_);
lean_inc_ref(v_options_2842_);
lean_inc_ref(v_fileMap_2841_);
lean_inc_ref(v_fileName_2840_);
v___x_2860_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2860_, 0, v_fileName_2840_);
lean_ctor_set(v___x_2860_, 1, v_fileMap_2841_);
lean_ctor_set(v___x_2860_, 2, v_options_2842_);
lean_ctor_set(v___x_2860_, 3, v_currRecDepth_2843_);
lean_ctor_set(v___x_2860_, 4, v_maxRecDepth_2844_);
lean_ctor_set(v___x_2860_, 5, v_ref_2859_);
lean_ctor_set(v___x_2860_, 6, v_currNamespace_2846_);
lean_ctor_set(v___x_2860_, 7, v_openDecls_2847_);
lean_ctor_set(v___x_2860_, 8, v_initHeartbeats_2848_);
lean_ctor_set(v___x_2860_, 9, v_maxHeartbeats_2849_);
lean_ctor_set(v___x_2860_, 10, v_quotContext_2850_);
lean_ctor_set(v___x_2860_, 11, v_currMacroScope_2851_);
lean_ctor_set(v___x_2860_, 12, v_cancelTk_x3f_2853_);
lean_ctor_set(v___x_2860_, 13, v_inheritedTraceOptions_2855_);
lean_ctor_set_uint8(v___x_2860_, sizeof(void*)*14, v_diag_2852_);
lean_ctor_set_uint8(v___x_2860_, sizeof(void*)*14 + 1, v_suppressElabErrors_2854_);
lean_inc(v_head_2838_);
lean_inc(v_id_2828_);
v___x_2861_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2831_, v_id_2828_, v_head_2838_, v___x_2857_, v_minIndexable_2829_, v___x_2856_, v___x_2858_, v___y_2832_, v___y_2833_, v___x_2860_, v___y_2835_);
lean_dec_ref_known(v___x_2860_, 14);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v_as_x27_2830_ = v_tail_2839_;
v_b_2831_ = v_a_2862_;
goto _start;
}
else
{
lean_dec(v_id_2828_);
return v___x_2861_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_2864_, lean_object* v_id_2865_, lean_object* v_minIndexable_2866_, lean_object* v_as_x27_2867_, lean_object* v_b_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
uint8_t v_minIndexable_boxed_2874_; lean_object* v_res_2875_; 
v_minIndexable_boxed_2874_ = lean_unbox(v_minIndexable_2866_);
v_res_2875_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_2864_, v_id_2865_, v_minIndexable_boxed_2874_, v_as_x27_2867_, v_b_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v_as_x27_2867_);
lean_dec(v_p_2864_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_2876_){
_start:
{
if (lean_obj_tag(v_x_2876_) == 0)
{
lean_object* v___x_2877_; 
v___x_2877_ = lean_box(0);
return v___x_2877_;
}
else
{
lean_object* v_head_2878_; lean_object* v_tail_2879_; lean_object* v_fst_2880_; uint8_t v___x_2881_; 
v_head_2878_ = lean_ctor_get(v_x_2876_, 0);
v_tail_2879_ = lean_ctor_get(v_x_2876_, 1);
v_fst_2880_ = lean_ctor_get(v_head_2878_, 0);
v___x_2881_ = l_Lean_isPrivateName(v_fst_2880_);
if (v___x_2881_ == 0)
{
v_x_2876_ = v_tail_2879_;
goto _start;
}
else
{
lean_object* v___x_2883_; 
lean_inc(v_head_2878_);
v___x_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2883_, 0, v_head_2878_);
return v___x_2883_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_2884_);
lean_dec(v_x_2884_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_2886_, lean_object* v_msgData_2887_, uint8_t v_severity_2888_, uint8_t v_isSilent_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; uint8_t v___y_2901_; uint8_t v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; uint8_t v___y_2936_; uint8_t v___y_2937_; uint8_t v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; uint8_t v___y_2961_; uint8_t v___y_2962_; uint8_t v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; uint8_t v___y_2972_; uint8_t v___y_2973_; uint8_t v___y_2974_; uint8_t v___x_2979_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; uint8_t v___y_2985_; uint8_t v___y_2986_; uint8_t v___y_2987_; uint8_t v___y_2989_; uint8_t v___x_3004_; 
v___x_2979_ = 2;
v___x_3004_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2888_, v___x_2979_);
if (v___x_3004_ == 0)
{
v___y_2989_ = v___x_3004_;
goto v___jp_2988_;
}
else
{
uint8_t v___x_3005_; 
lean_inc_ref(v_msgData_2887_);
v___x_3005_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2887_);
v___y_2989_ = v___x_3005_;
goto v___jp_2988_;
}
v___jp_2895_:
{
lean_object* v___x_2905_; lean_object* v_currNamespace_2906_; lean_object* v_openDecls_2907_; lean_object* v_env_2908_; lean_object* v_nextMacroScope_2909_; lean_object* v_ngen_2910_; lean_object* v_auxDeclNGen_2911_; lean_object* v_traceState_2912_; lean_object* v_cache_2913_; lean_object* v_messages_2914_; lean_object* v_infoState_2915_; lean_object* v_snapshotTasks_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2930_; 
v___x_2905_ = lean_st_ref_take(v___y_2904_);
v_currNamespace_2906_ = lean_ctor_get(v___y_2903_, 6);
v_openDecls_2907_ = lean_ctor_get(v___y_2903_, 7);
v_env_2908_ = lean_ctor_get(v___x_2905_, 0);
v_nextMacroScope_2909_ = lean_ctor_get(v___x_2905_, 1);
v_ngen_2910_ = lean_ctor_get(v___x_2905_, 2);
v_auxDeclNGen_2911_ = lean_ctor_get(v___x_2905_, 3);
v_traceState_2912_ = lean_ctor_get(v___x_2905_, 4);
v_cache_2913_ = lean_ctor_get(v___x_2905_, 5);
v_messages_2914_ = lean_ctor_get(v___x_2905_, 6);
v_infoState_2915_ = lean_ctor_get(v___x_2905_, 7);
v_snapshotTasks_2916_ = lean_ctor_get(v___x_2905_, 8);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2918_ = v___x_2905_;
v_isShared_2919_ = v_isSharedCheck_2930_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_snapshotTasks_2916_);
lean_inc(v_infoState_2915_);
lean_inc(v_messages_2914_);
lean_inc(v_cache_2913_);
lean_inc(v_traceState_2912_);
lean_inc(v_auxDeclNGen_2911_);
lean_inc(v_ngen_2910_);
lean_inc(v_nextMacroScope_2909_);
lean_inc(v_env_2908_);
lean_dec(v___x_2905_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2930_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2925_; 
lean_inc(v_openDecls_2907_);
lean_inc(v_currNamespace_2906_);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v_currNamespace_2906_);
lean_ctor_set(v___x_2920_, 1, v_openDecls_2907_);
v___x_2921_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
lean_ctor_set(v___x_2921_, 1, v___y_2897_);
lean_inc_ref(v___y_2899_);
lean_inc_ref(v___y_2898_);
v___x_2922_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2922_, 0, v___y_2898_);
lean_ctor_set(v___x_2922_, 1, v___y_2900_);
lean_ctor_set(v___x_2922_, 2, v___y_2896_);
lean_ctor_set(v___x_2922_, 3, v___y_2899_);
lean_ctor_set(v___x_2922_, 4, v___x_2921_);
lean_ctor_set_uint8(v___x_2922_, sizeof(void*)*5, v___y_2902_);
lean_ctor_set_uint8(v___x_2922_, sizeof(void*)*5 + 1, v___y_2901_);
lean_ctor_set_uint8(v___x_2922_, sizeof(void*)*5 + 2, v_isSilent_2889_);
v___x_2923_ = l_Lean_MessageLog_add(v___x_2922_, v_messages_2914_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 6, v___x_2923_);
v___x_2925_ = v___x_2918_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_env_2908_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_nextMacroScope_2909_);
lean_ctor_set(v_reuseFailAlloc_2929_, 2, v_ngen_2910_);
lean_ctor_set(v_reuseFailAlloc_2929_, 3, v_auxDeclNGen_2911_);
lean_ctor_set(v_reuseFailAlloc_2929_, 4, v_traceState_2912_);
lean_ctor_set(v_reuseFailAlloc_2929_, 5, v_cache_2913_);
lean_ctor_set(v_reuseFailAlloc_2929_, 6, v___x_2923_);
lean_ctor_set(v_reuseFailAlloc_2929_, 7, v_infoState_2915_);
lean_ctor_set(v_reuseFailAlloc_2929_, 8, v_snapshotTasks_2916_);
v___x_2925_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = lean_st_ref_set(v___y_2904_, v___x_2925_);
v___x_2927_ = lean_box(0);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
}
}
v___jp_2931_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2955_; 
v___x_2940_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2887_);
v___x_2941_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_2940_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2955_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2955_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
lean_inc_ref_n(v___y_2934_, 2);
v___x_2946_ = l_Lean_FileMap_toPosition(v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
v___x_2947_ = l_Lean_FileMap_toPosition(v___y_2934_, v___y_2939_);
lean_dec(v___y_2939_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
v___x_2949_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_2936_ == 0)
{
lean_del_object(v___x_2944_);
lean_dec_ref(v___y_2932_);
v___y_2896_ = v___x_2948_;
v___y_2897_ = v_a_2942_;
v___y_2898_ = v___y_2933_;
v___y_2899_ = v___x_2949_;
v___y_2900_ = v___x_2946_;
v___y_2901_ = v___y_2937_;
v___y_2902_ = v___y_2938_;
v___y_2903_ = v___y_2892_;
v___y_2904_ = v___y_2893_;
goto v___jp_2895_;
}
else
{
uint8_t v___x_2950_; 
lean_inc(v_a_2942_);
v___x_2950_ = l_Lean_MessageData_hasTag(v___y_2932_, v_a_2942_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2953_; 
lean_dec_ref_known(v___x_2948_, 1);
lean_dec_ref(v___x_2946_);
lean_dec(v_a_2942_);
v___x_2951_ = lean_box(0);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v___x_2951_);
v___x_2953_ = v___x_2944_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
else
{
lean_del_object(v___x_2944_);
v___y_2896_ = v___x_2948_;
v___y_2897_ = v_a_2942_;
v___y_2898_ = v___y_2933_;
v___y_2899_ = v___x_2949_;
v___y_2900_ = v___x_2946_;
v___y_2901_ = v___y_2937_;
v___y_2902_ = v___y_2938_;
v___y_2903_ = v___y_2892_;
v___y_2904_ = v___y_2893_;
goto v___jp_2895_;
}
}
}
}
v___jp_2956_:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Syntax_getTailPos_x3f(v___y_2960_, v___y_2963_);
lean_dec(v___y_2960_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_inc(v___y_2964_);
v___y_2932_ = v___y_2957_;
v___y_2933_ = v___y_2958_;
v___y_2934_ = v___y_2959_;
v___y_2935_ = v___y_2964_;
v___y_2936_ = v___y_2961_;
v___y_2937_ = v___y_2962_;
v___y_2938_ = v___y_2963_;
v___y_2939_ = v___y_2964_;
goto v___jp_2931_;
}
else
{
lean_object* v_val_2966_; 
v_val_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_val_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v___y_2932_ = v___y_2957_;
v___y_2933_ = v___y_2958_;
v___y_2934_ = v___y_2959_;
v___y_2935_ = v___y_2964_;
v___y_2936_ = v___y_2961_;
v___y_2937_ = v___y_2962_;
v___y_2938_ = v___y_2963_;
v___y_2939_ = v_val_2966_;
goto v___jp_2931_;
}
}
v___jp_2967_:
{
lean_object* v_ref_2975_; lean_object* v___x_2976_; 
v_ref_2975_ = l_Lean_replaceRef(v_ref_2886_, v___y_2970_);
v___x_2976_ = l_Lean_Syntax_getPos_x3f(v_ref_2975_, v___y_2973_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_unsigned_to_nat(0u);
v___y_2957_ = v___y_2968_;
v___y_2958_ = v___y_2969_;
v___y_2959_ = v___y_2971_;
v___y_2960_ = v_ref_2975_;
v___y_2961_ = v___y_2972_;
v___y_2962_ = v___y_2974_;
v___y_2963_ = v___y_2973_;
v___y_2964_ = v___x_2977_;
goto v___jp_2956_;
}
else
{
lean_object* v_val_2978_; 
v_val_2978_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_val_2978_);
lean_dec_ref_known(v___x_2976_, 1);
v___y_2957_ = v___y_2968_;
v___y_2958_ = v___y_2969_;
v___y_2959_ = v___y_2971_;
v___y_2960_ = v_ref_2975_;
v___y_2961_ = v___y_2972_;
v___y_2962_ = v___y_2974_;
v___y_2963_ = v___y_2973_;
v___y_2964_ = v_val_2978_;
goto v___jp_2956_;
}
}
v___jp_2980_:
{
if (v___y_2987_ == 0)
{
v___y_2968_ = v___y_2984_;
v___y_2969_ = v___y_2982_;
v___y_2970_ = v___y_2981_;
v___y_2971_ = v___y_2983_;
v___y_2972_ = v___y_2985_;
v___y_2973_ = v___y_2986_;
v___y_2974_ = v_severity_2888_;
goto v___jp_2967_;
}
else
{
v___y_2968_ = v___y_2984_;
v___y_2969_ = v___y_2982_;
v___y_2970_ = v___y_2981_;
v___y_2971_ = v___y_2983_;
v___y_2972_ = v___y_2985_;
v___y_2973_ = v___y_2986_;
v___y_2974_ = v___x_2979_;
goto v___jp_2967_;
}
}
v___jp_2988_:
{
if (v___y_2989_ == 0)
{
lean_object* v_fileName_2990_; lean_object* v_fileMap_2991_; lean_object* v_options_2992_; lean_object* v_ref_2993_; uint8_t v_suppressElabErrors_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___f_2997_; uint8_t v___x_2998_; uint8_t v___x_2999_; 
v_fileName_2990_ = lean_ctor_get(v___y_2892_, 0);
v_fileMap_2991_ = lean_ctor_get(v___y_2892_, 1);
v_options_2992_ = lean_ctor_get(v___y_2892_, 2);
v_ref_2993_ = lean_ctor_get(v___y_2892_, 5);
v_suppressElabErrors_2994_ = lean_ctor_get_uint8(v___y_2892_, sizeof(void*)*14 + 1);
v___x_2995_ = lean_box(v___y_2989_);
v___x_2996_ = lean_box(v_suppressElabErrors_2994_);
v___f_2997_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2997_, 0, v___x_2995_);
lean_closure_set(v___f_2997_, 1, v___x_2996_);
v___x_2998_ = 1;
v___x_2999_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2888_, v___x_2998_);
if (v___x_2999_ == 0)
{
v___y_2981_ = v_ref_2993_;
v___y_2982_ = v_fileName_2990_;
v___y_2983_ = v_fileMap_2991_;
v___y_2984_ = v___f_2997_;
v___y_2985_ = v_suppressElabErrors_2994_;
v___y_2986_ = v___y_2989_;
v___y_2987_ = v___x_2999_;
goto v___jp_2980_;
}
else
{
lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_3000_ = l_Lean_warningAsError;
v___x_3001_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2992_, v___x_3000_);
v___y_2981_ = v_ref_2993_;
v___y_2982_ = v_fileName_2990_;
v___y_2983_ = v_fileMap_2991_;
v___y_2984_ = v___f_2997_;
v___y_2985_ = v_suppressElabErrors_2994_;
v___y_2986_ = v___y_2989_;
v___y_2987_ = v___x_3001_;
goto v___jp_2980_;
}
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec_ref(v_msgData_2887_);
v___x_3002_ = lean_box(0);
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
return v___x_3003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_3006_, lean_object* v_msgData_3007_, lean_object* v_severity_3008_, lean_object* v_isSilent_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
uint8_t v_severity_boxed_3015_; uint8_t v_isSilent_boxed_3016_; lean_object* v_res_3017_; 
v_severity_boxed_3015_ = lean_unbox(v_severity_3008_);
v_isSilent_boxed_3016_ = lean_unbox(v_isSilent_3009_);
v_res_3017_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3006_, v_msgData_3007_, v_severity_boxed_3015_, v_isSilent_boxed_3016_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v_ref_3006_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_3018_, uint8_t v_severity_3019_, uint8_t v_isSilent_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_ref_3028_; lean_object* v___x_3029_; 
v_ref_3028_ = lean_ctor_get(v___y_3025_, 5);
v___x_3029_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3028_, v_msgData_3018_, v_severity_3019_, v_isSilent_3020_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_3030_, lean_object* v_severity_3031_, lean_object* v_isSilent_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
uint8_t v_severity_boxed_3040_; uint8_t v_isSilent_boxed_3041_; lean_object* v_res_3042_; 
v_severity_boxed_3040_ = lean_unbox(v_severity_3031_);
v_isSilent_boxed_3041_ = lean_unbox(v_isSilent_3032_);
v_res_3042_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3030_, v_severity_boxed_3040_, v_isSilent_boxed_3041_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
uint8_t v___x_3051_; uint8_t v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = 1;
v___x_3052_ = 0;
v___x_3053_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3043_, v___x_3051_, v___x_3052_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_options_3066_; uint8_t v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_options_3066_ = lean_ctor_get(v___y_3064_, 2);
v___x_3067_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_3066_, v_opt_3063_);
v___x_3068_ = lean_box(v___x_3067_);
v___x_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3070_, v___y_3071_);
lean_dec_ref(v___y_3071_);
lean_dec_ref(v_opt_3070_);
return v_res_3073_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3076_ = l_Lean_stringToMessageData(v___x_3075_);
return v___x_3076_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3079_ = l_Lean_stringToMessageData(v___x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; lean_object* v_env_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3111_; 
v___x_3088_ = lean_st_ref_get(v___y_3086_);
v_env_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc_ref(v_env_3089_);
lean_dec(v___x_3088_);
v___x_3090_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3091_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3090_, v___y_3085_);
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3111_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3111_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
uint8_t v_isExporting_3101_; 
v_isExporting_3101_ = lean_ctor_get_uint8(v_env_3089_, sizeof(void*)*8);
lean_dec_ref(v_env_3089_);
if (v_isExporting_3101_ == 0)
{
lean_dec(v_a_3092_);
lean_dec(v_id_3080_);
goto v___jp_3096_;
}
else
{
uint8_t v___x_3102_; 
v___x_3102_ = l_Lean_isPrivateName(v_id_3080_);
if (v___x_3102_ == 0)
{
lean_dec(v_a_3092_);
lean_dec(v_id_3080_);
goto v___jp_3096_;
}
else
{
uint8_t v___x_3103_; 
v___x_3103_ = lean_unbox(v_a_3092_);
lean_dec(v_a_3092_);
if (v___x_3103_ == 0)
{
lean_dec(v_id_3080_);
goto v___jp_3096_;
}
else
{
lean_object* v___x_3104_; uint8_t v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
lean_del_object(v___x_3094_);
v___x_3104_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3105_ = 0;
v___x_3106_ = l_Lean_MessageData_ofConstName(v_id_3080_, v___x_3105_);
v___x_3107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3104_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3107_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3109_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
return v___x_3110_;
}
}
}
v___jp_3096_:
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3097_ = lean_box(0);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3097_);
v___x_3099_ = v___x_3094_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3121_, uint8_t v_enableLog_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___x_3130_; lean_object* v_env_3131_; lean_object* v_options_3132_; lean_object* v_currNamespace_3133_; lean_object* v_openDecls_3134_; lean_object* v___x_3135_; lean_object* v_env_3136_; lean_object* v_res_3137_; 
v___x_3130_ = lean_st_ref_get(v___y_3128_);
v_env_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc_ref(v_env_3131_);
lean_dec(v___x_3130_);
v_options_3132_ = lean_ctor_get(v___y_3127_, 2);
v_currNamespace_3133_ = lean_ctor_get(v___y_3127_, 6);
v_openDecls_3134_ = lean_ctor_get(v___y_3127_, 7);
v___x_3135_ = lean_st_ref_get(v___y_3128_);
v_env_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc_ref(v_env_3136_);
lean_dec(v___x_3135_);
lean_inc(v_openDecls_3134_);
lean_inc(v_currNamespace_3133_);
v_res_3137_ = l_Lean_ResolveName_resolveGlobalName(v_env_3131_, v_options_3132_, v_currNamespace_3133_, v_openDecls_3134_, v_id_3121_);
if (v_enableLog_3122_ == 0)
{
lean_object* v___x_3138_; 
lean_dec_ref(v_env_3136_);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_res_3137_);
return v___x_3138_;
}
else
{
uint8_t v_isExporting_3139_; 
v_isExporting_3139_ = lean_ctor_get_uint8(v_env_3136_, sizeof(void*)*8);
lean_dec_ref(v_env_3136_);
if (v_isExporting_3139_ == 0)
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_res_3137_);
return v___x_3140_;
}
else
{
lean_object* v___x_3141_; 
v___x_3141_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3137_);
if (lean_obj_tag(v___x_3141_) == 1)
{
lean_object* v_val_3142_; lean_object* v_fst_3143_; lean_object* v___x_3144_; 
v_val_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_val_3142_);
lean_dec_ref_known(v___x_3141_, 1);
v_fst_3143_ = lean_ctor_get(v_val_3142_, 0);
lean_inc(v_fst_3143_);
lean_dec(v_val_3142_);
v___x_3144_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3143_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v___x_3144_, 0);
lean_dec(v_unused_3152_);
v___x_3146_ = v___x_3144_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_dec(v___x_3144_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v_res_3137_);
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_res_3137_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v_res_3137_);
v_a_3153_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3144_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3144_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
else
{
lean_object* v___x_3161_; 
lean_dec(v___x_3141_);
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v_res_3137_);
return v___x_3161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3162_, lean_object* v_enableLog_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
uint8_t v_enableLog_boxed_3171_; lean_object* v_res_3172_; 
v_enableLog_boxed_3171_ = lean_unbox(v_enableLog_3163_);
v_res_3172_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3162_, v_enableLog_boxed_3171_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
if (lean_obj_tag(v_a_3173_) == 0)
{
lean_object* v___x_3175_; 
v___x_3175_ = l_List_reverse___redArg(v_a_3174_);
return v___x_3175_;
}
else
{
lean_object* v_head_3176_; lean_object* v_tail_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3188_; 
v_head_3176_ = lean_ctor_get(v_a_3173_, 0);
v_tail_3177_ = lean_ctor_get(v_a_3173_, 1);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_a_3173_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3179_ = v_a_3173_;
v_isShared_3180_ = v_isSharedCheck_3188_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_tail_3177_);
lean_inc(v_head_3176_);
lean_dec(v_a_3173_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3188_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v_snd_3181_; uint8_t v___x_3182_; 
v_snd_3181_ = lean_ctor_get(v_head_3176_, 1);
v___x_3182_ = l_List_isEmpty___redArg(v_snd_3181_);
if (v___x_3182_ == 0)
{
lean_del_object(v___x_3179_);
lean_dec(v_head_3176_);
v_a_3173_ = v_tail_3177_;
goto _start;
}
else
{
lean_object* v___x_3185_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 1, v_a_3174_);
v___x_3185_ = v___x_3179_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_head_3176_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_a_3174_);
v___x_3185_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
v_a_3173_ = v_tail_3177_;
v_a_3174_ = v___x_3185_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3189_, lean_object* v_findLocalDecl_x3f_3190_, lean_object* v_n_3191_, lean_object* v_projs_3192_, uint8_t v_globalDeclFound_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v___y_3202_; lean_object* v___y_3203_; uint8_t v_globalDeclFoundNext_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v_imported_3213_; lean_object* v_ctx_3214_; lean_object* v_scopes_3215_; lean_object* v_givenNameView_3216_; uint8_t v___y_3218_; 
v_imported_3213_ = lean_ctor_get(v_view_3189_, 1);
v_ctx_3214_ = lean_ctor_get(v_view_3189_, 2);
v_scopes_3215_ = lean_ctor_get(v_view_3189_, 3);
lean_inc(v_scopes_3215_);
lean_inc(v_ctx_3214_);
lean_inc(v_imported_3213_);
lean_inc(v_n_3191_);
v_givenNameView_3216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3216_, 0, v_n_3191_);
lean_ctor_set(v_givenNameView_3216_, 1, v_imported_3213_);
lean_ctor_set(v_givenNameView_3216_, 2, v_ctx_3214_);
lean_ctor_set(v_givenNameView_3216_, 3, v_scopes_3215_);
if (v_globalDeclFound_3193_ == 0)
{
v___y_3218_ = v_globalDeclFound_3193_;
goto v___jp_3217_;
}
else
{
uint8_t v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = l_List_isEmpty___redArg(v_projs_3192_);
v___x_3254_ = lean_bool_not(v___x_3253_);
v___y_3218_ = v___x_3254_;
goto v___jp_3217_;
}
v___jp_3201_:
{
lean_object* v___x_3211_; 
v___x_3211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___y_3203_);
lean_ctor_set(v___x_3211_, 1, v_projs_3192_);
v_n_3191_ = v___y_3202_;
v_projs_3192_ = v___x_3211_;
v_globalDeclFound_3193_ = v_globalDeclFoundNext_3204_;
v___y_3194_ = v___y_3205_;
v___y_3195_ = v___y_3206_;
v___y_3196_ = v___y_3207_;
v___y_3197_ = v___y_3208_;
v___y_3198_ = v___y_3209_;
v___y_3199_ = v___y_3210_;
goto _start;
}
v___jp_3217_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = lean_box(v___y_3218_);
lean_inc_ref(v_findLocalDecl_x3f_3190_);
lean_inc_ref(v_givenNameView_3216_);
v___x_3220_ = lean_apply_2(v_findLocalDecl_x3f_3190_, v_givenNameView_3216_, v___x_3219_);
if (lean_obj_tag(v___x_3220_) == 0)
{
if (lean_obj_tag(v_n_3191_) == 1)
{
if (v_globalDeclFound_3193_ == 0)
{
lean_object* v_pre_3221_; lean_object* v_str_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v_pre_3221_ = lean_ctor_get(v_n_3191_, 0);
lean_inc(v_pre_3221_);
v_str_3222_ = lean_ctor_get(v_n_3191_, 1);
lean_inc_ref(v_str_3222_);
lean_dec_ref_known(v_n_3191_, 2);
v___x_3223_ = l_Lean_MacroScopesView_review(v_givenNameView_3216_);
v___x_3224_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3223_, v_globalDeclFound_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3226_; lean_object* v_r_3227_; uint8_t v___x_3228_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v___x_3226_ = lean_box(0);
v_r_3227_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3225_, v___x_3226_);
v___x_3228_ = l_List_isEmpty___redArg(v_r_3227_);
lean_dec(v_r_3227_);
if (v___x_3228_ == 0)
{
uint8_t v_globalDeclFoundNext_3229_; 
v_globalDeclFoundNext_3229_ = 1;
v___y_3202_ = v_pre_3221_;
v___y_3203_ = v_str_3222_;
v_globalDeclFoundNext_3204_ = v_globalDeclFoundNext_3229_;
v___y_3205_ = v___y_3194_;
v___y_3206_ = v___y_3195_;
v___y_3207_ = v___y_3196_;
v___y_3208_ = v___y_3197_;
v___y_3209_ = v___y_3198_;
v___y_3210_ = v___y_3199_;
goto v___jp_3201_;
}
else
{
v___y_3202_ = v_pre_3221_;
v___y_3203_ = v_str_3222_;
v_globalDeclFoundNext_3204_ = v_globalDeclFound_3193_;
v___y_3205_ = v___y_3194_;
v___y_3206_ = v___y_3195_;
v___y_3207_ = v___y_3196_;
v___y_3208_ = v___y_3197_;
v___y_3209_ = v___y_3198_;
v___y_3210_ = v___y_3199_;
goto v___jp_3201_;
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v_str_3222_);
lean_dec(v_pre_3221_);
lean_dec(v_projs_3192_);
lean_dec_ref(v_findLocalDecl_x3f_3190_);
v_a_3230_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3224_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3224_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_object* v_pre_3238_; lean_object* v_str_3239_; 
lean_dec_ref_known(v_givenNameView_3216_, 4);
v_pre_3238_ = lean_ctor_get(v_n_3191_, 0);
lean_inc(v_pre_3238_);
v_str_3239_ = lean_ctor_get(v_n_3191_, 1);
lean_inc_ref(v_str_3239_);
lean_dec_ref_known(v_n_3191_, 2);
v___y_3202_ = v_pre_3238_;
v___y_3203_ = v_str_3239_;
v_globalDeclFoundNext_3204_ = v_globalDeclFound_3193_;
v___y_3205_ = v___y_3194_;
v___y_3206_ = v___y_3195_;
v___y_3207_ = v___y_3196_;
v___y_3208_ = v___y_3197_;
v___y_3209_ = v___y_3198_;
v___y_3210_ = v___y_3199_;
goto v___jp_3201_;
}
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
lean_dec_ref_known(v_givenNameView_3216_, 4);
lean_dec(v_projs_3192_);
lean_dec(v_n_3191_);
lean_dec_ref(v_findLocalDecl_x3f_3190_);
v___x_3240_ = lean_box(0);
v___x_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
return v___x_3241_;
}
}
else
{
lean_object* v_val_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref_known(v_givenNameView_3216_, 4);
lean_dec(v_n_3191_);
lean_dec_ref(v_findLocalDecl_x3f_3190_);
v_val_3242_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3244_ = v___x_3220_;
v_isShared_3245_ = v_isSharedCheck_3252_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_val_3242_);
lean_dec(v___x_3220_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3252_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3246_ = l_Lean_LocalDecl_toExpr(v_val_3242_);
v___x_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
lean_ctor_set(v___x_3247_, 1, v_projs_3192_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v___x_3247_);
v___x_3249_ = v___x_3244_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
return v___x_3250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3255_, lean_object* v_findLocalDecl_x3f_3256_, lean_object* v_n_3257_, lean_object* v_projs_3258_, lean_object* v_globalDeclFound_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
uint8_t v_globalDeclFound_boxed_3267_; lean_object* v_res_3268_; 
v_globalDeclFound_boxed_3267_ = lean_unbox(v_globalDeclFound_3259_);
v_res_3268_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3255_, v_findLocalDecl_x3f_3256_, v_n_3257_, v_projs_3258_, v_globalDeclFound_boxed_3267_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec_ref(v_view_3255_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3269_, lean_object* v_givenName_3270_, lean_object* v_as_3271_, lean_object* v_i_3272_){
_start:
{
lean_object* v_zero_3273_; uint8_t v_isZero_3274_; 
v_zero_3273_ = lean_unsigned_to_nat(0u);
v_isZero_3274_ = lean_nat_dec_eq(v_i_3272_, v_zero_3273_);
if (v_isZero_3274_ == 1)
{
lean_object* v___x_3275_; 
lean_dec(v_i_3272_);
v___x_3275_ = lean_box(0);
return v___x_3275_;
}
else
{
lean_object* v_one_3276_; lean_object* v_n_3277_; lean_object* v___y_3279_; lean_object* v___x_3281_; 
v_one_3276_ = lean_unsigned_to_nat(1u);
v_n_3277_ = lean_nat_sub(v_i_3272_, v_one_3276_);
lean_dec(v_i_3272_);
v___x_3281_ = lean_array_fget_borrowed(v_as_3271_, v_n_3277_);
if (lean_obj_tag(v___x_3281_) == 0)
{
v___y_3279_ = v___x_3281_;
goto v___jp_3278_;
}
else
{
lean_object* v_val_3282_; uint8_t v___x_3283_; 
v_val_3282_ = lean_ctor_get(v___x_3281_, 0);
v___x_3283_ = l_Lean_LocalDecl_isAuxDecl(v_val_3282_);
if (v___x_3283_ == 0)
{
v___y_3279_ = v_localDecl_x3f_3269_;
goto v___jp_3278_;
}
else
{
lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3284_ = l_Lean_LocalDecl_userName(v_val_3282_);
v___x_3285_ = lean_name_eq(v___x_3284_, v_givenName_3270_);
lean_dec(v___x_3284_);
if (v___x_3285_ == 0)
{
v_i_3272_ = v_n_3277_;
goto _start;
}
else
{
v___y_3279_ = v___x_3281_;
goto v___jp_3278_;
}
}
}
v___jp_3278_:
{
if (lean_obj_tag(v___y_3279_) == 0)
{
v_i_3272_ = v_n_3277_;
goto _start;
}
else
{
lean_dec(v_n_3277_);
lean_inc_ref(v___y_3279_);
return v___y_3279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3287_, lean_object* v_givenName_3288_, lean_object* v_as_3289_, lean_object* v_i_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3287_, v_givenName_3288_, v_as_3289_, v_i_3290_);
lean_dec_ref(v_as_3289_);
lean_dec(v_givenName_3288_);
lean_dec(v_localDecl_x3f_3287_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3292_, lean_object* v_givenName_3293_, lean_object* v_as_3294_, lean_object* v_i_3295_){
_start:
{
lean_object* v_zero_3296_; uint8_t v_isZero_3297_; 
v_zero_3296_ = lean_unsigned_to_nat(0u);
v_isZero_3297_ = lean_nat_dec_eq(v_i_3295_, v_zero_3296_);
if (v_isZero_3297_ == 1)
{
lean_object* v___x_3298_; 
lean_dec(v_i_3295_);
v___x_3298_ = lean_box(0);
return v___x_3298_;
}
else
{
lean_object* v_one_3299_; lean_object* v_n_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_one_3299_ = lean_unsigned_to_nat(1u);
v_n_3300_ = lean_nat_sub(v_i_3295_, v_one_3299_);
lean_dec(v_i_3295_);
v___x_3301_ = lean_array_fget_borrowed(v_as_3294_, v_n_3300_);
v___x_3302_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3292_, v_givenName_3293_, v___x_3301_);
if (lean_obj_tag(v___x_3302_) == 0)
{
v_i_3295_ = v_n_3300_;
goto _start;
}
else
{
lean_dec(v_n_3300_);
return v___x_3302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3304_, lean_object* v_givenName_3305_, lean_object* v_x_3306_){
_start:
{
if (lean_obj_tag(v_x_3306_) == 0)
{
lean_object* v_cs_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v_cs_3307_ = lean_ctor_get(v_x_3306_, 0);
v___x_3308_ = lean_array_get_size(v_cs_3307_);
v___x_3309_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3304_, v_givenName_3305_, v_cs_3307_, v___x_3308_);
return v___x_3309_;
}
else
{
lean_object* v_vs_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_vs_3310_ = lean_ctor_get(v_x_3306_, 0);
v___x_3311_ = lean_array_get_size(v_vs_3310_);
v___x_3312_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3304_, v_givenName_3305_, v_vs_3310_, v___x_3311_);
return v___x_3312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3313_, lean_object* v_givenName_3314_, lean_object* v_x_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3313_, v_givenName_3314_, v_x_3315_);
lean_dec_ref(v_x_3315_);
lean_dec(v_givenName_3314_);
lean_dec(v_localDecl_x3f_3313_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3317_, lean_object* v_givenName_3318_, lean_object* v_as_3319_, lean_object* v_i_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3317_, v_givenName_3318_, v_as_3319_, v_i_3320_);
lean_dec_ref(v_as_3319_);
lean_dec(v_givenName_3318_);
lean_dec(v_localDecl_x3f_3317_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3322_, lean_object* v_givenName_3323_, lean_object* v_t_3324_){
_start:
{
lean_object* v_root_3325_; lean_object* v_tail_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v_root_3325_ = lean_ctor_get(v_t_3324_, 0);
v_tail_3326_ = lean_ctor_get(v_t_3324_, 1);
v___x_3327_ = lean_array_get_size(v_tail_3326_);
v___x_3328_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3322_, v_givenName_3323_, v_tail_3326_, v___x_3327_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3322_, v_givenName_3323_, v_root_3325_);
return v___x_3329_;
}
else
{
return v___x_3328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3330_, lean_object* v_givenName_3331_, lean_object* v_t_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3330_, v_givenName_3331_, v_t_3332_);
lean_dec_ref(v_t_3332_);
lean_dec(v_givenName_3331_);
lean_dec(v_localDecl_x3f_3330_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3334_, lean_object* v_k_3335_){
_start:
{
if (lean_obj_tag(v_t_3334_) == 0)
{
lean_object* v_k_3336_; lean_object* v_v_3337_; lean_object* v_l_3338_; lean_object* v_r_3339_; uint8_t v___x_3340_; 
v_k_3336_ = lean_ctor_get(v_t_3334_, 1);
v_v_3337_ = lean_ctor_get(v_t_3334_, 2);
v_l_3338_ = lean_ctor_get(v_t_3334_, 3);
v_r_3339_ = lean_ctor_get(v_t_3334_, 4);
v___x_3340_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3335_, v_k_3336_);
switch(v___x_3340_)
{
case 0:
{
v_t_3334_ = v_l_3338_;
goto _start;
}
case 1:
{
lean_object* v___x_3342_; 
lean_inc(v_v_3337_);
v___x_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3342_, 0, v_v_3337_);
return v___x_3342_;
}
default: 
{
v_t_3334_ = v_r_3339_;
goto _start;
}
}
}
else
{
lean_object* v___x_3344_; 
v___x_3344_ = lean_box(0);
return v___x_3344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3345_, lean_object* v_k_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3345_, v_k_3346_);
lean_dec(v_k_3346_);
lean_dec(v_t_3345_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3348_, lean_object* v_givenName_3349_){
_start:
{
lean_object* v___x_3350_; uint8_t v___x_3351_; 
v___x_3350_ = l_Lean_LocalDecl_userName(v_localDecl_3348_);
v___x_3351_ = lean_name_eq(v___x_3350_, v_givenName_3349_);
lean_dec(v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; 
lean_dec_ref(v_localDecl_3348_);
v___x_3352_ = lean_box(0);
return v___x_3352_;
}
else
{
lean_object* v___x_3353_; 
v___x_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3353_, 0, v_localDecl_3348_);
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3354_, lean_object* v_givenName_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3354_, v_givenName_3355_);
lean_dec(v_givenName_3355_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3357_, uint8_t v_skipAuxDecl_3358_, lean_object* v_auxDeclToFullName_3359_, lean_object* v___x_3360_, lean_object* v_givenNameView_3361_, lean_object* v_as_3362_, lean_object* v_i_3363_){
_start:
{
lean_object* v_zero_3364_; uint8_t v_isZero_3365_; 
v_zero_3364_ = lean_unsigned_to_nat(0u);
v_isZero_3365_ = lean_nat_dec_eq(v_i_3363_, v_zero_3364_);
if (v_isZero_3365_ == 1)
{
lean_object* v___x_3366_; 
lean_dec(v_i_3363_);
lean_dec_ref(v_givenNameView_3361_);
lean_dec(v___x_3360_);
v___x_3366_ = lean_box(0);
return v___x_3366_;
}
else
{
lean_object* v_one_3367_; lean_object* v_n_3368_; lean_object* v___y_3370_; lean_object* v___x_3372_; 
v_one_3367_ = lean_unsigned_to_nat(1u);
v_n_3368_ = lean_nat_sub(v_i_3363_, v_one_3367_);
lean_dec(v_i_3363_);
v___x_3372_ = lean_array_fget_borrowed(v_as_3362_, v_n_3368_);
if (lean_obj_tag(v___x_3372_) == 0)
{
v___y_3370_ = v___x_3372_;
goto v___jp_3369_;
}
else
{
lean_object* v_val_3373_; uint8_t v___x_3374_; 
v_val_3373_ = lean_ctor_get(v___x_3372_, 0);
v___x_3374_ = l_Lean_LocalDecl_isAuxDecl(v_val_3373_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; 
lean_inc(v_val_3373_);
v___x_3375_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3373_, v_givenName_3357_);
v___y_3370_ = v___x_3375_;
goto v___jp_3369_;
}
else
{
uint8_t v___x_3376_; 
v___x_3376_ = lean_bool_not(v_skipAuxDecl_3358_);
if (v___x_3376_ == 0)
{
v_i_3363_ = v_n_3368_;
goto _start;
}
else
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = l_Lean_LocalDecl_fvarId(v_val_3373_);
v___x_3379_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3359_, v___x_3378_);
lean_dec(v___x_3378_);
if (lean_obj_tag(v___x_3379_) == 1)
{
lean_object* v_val_3380_; lean_object* v_fullDeclView_3381_; lean_object* v___y_3383_; lean_object* v_name_3404_; lean_object* v___x_3405_; 
v_val_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_val_3380_);
lean_dec_ref_known(v___x_3379_, 1);
v_fullDeclView_3381_ = l_Lean_extractMacroScopes(v_val_3380_);
v_name_3404_ = lean_ctor_get(v_fullDeclView_3381_, 0);
lean_inc_n(v_name_3404_, 2);
v___x_3405_ = l_Lean_privateToUserName_x3f(v_name_3404_);
if (lean_obj_tag(v___x_3405_) == 0)
{
v___y_3383_ = v_name_3404_;
goto v___jp_3382_;
}
else
{
lean_object* v_val_3406_; 
lean_dec(v_name_3404_);
v_val_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_val_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___y_3383_ = v_val_3406_;
goto v___jp_3382_;
}
v___jp_3382_:
{
lean_object* v_imported_3384_; lean_object* v_ctx_3385_; lean_object* v_scopes_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3402_; 
v_imported_3384_ = lean_ctor_get(v_fullDeclView_3381_, 1);
v_ctx_3385_ = lean_ctor_get(v_fullDeclView_3381_, 2);
v_scopes_3386_ = lean_ctor_get(v_fullDeclView_3381_, 3);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_fullDeclView_3381_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; 
v_unused_3403_ = lean_ctor_get(v_fullDeclView_3381_, 0);
lean_dec(v_unused_3403_);
v___x_3388_ = v_fullDeclView_3381_;
v_isShared_3389_ = v_isSharedCheck_3402_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_scopes_3386_);
lean_inc(v_ctx_3385_);
lean_inc(v_imported_3384_);
lean_dec(v_fullDeclView_3381_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3402_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v_fullDeclView_3391_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___y_3383_);
v_fullDeclView_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___y_3383_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_imported_3384_);
lean_ctor_set(v_reuseFailAlloc_3401_, 2, v_ctx_3385_);
lean_ctor_set(v_reuseFailAlloc_3401_, 3, v_scopes_3386_);
v_fullDeclView_3391_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v_fullDeclName_3392_; uint8_t v___x_3393_; 
lean_inc_ref(v_fullDeclView_3391_);
v_fullDeclName_3392_ = l_Lean_MacroScopesView_review(v_fullDeclView_3391_);
v___x_3393_ = l_Lean_Name_isPrefixOf(v___x_3360_, v_fullDeclName_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
lean_dec_ref(v_fullDeclView_3391_);
lean_inc(v___x_3360_);
lean_inc_ref(v_givenNameView_3361_);
lean_inc(v_val_3373_);
v___x_3394_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3373_, v_givenNameView_3361_, v_fullDeclName_3392_, v___x_3360_);
lean_dec(v_fullDeclName_3392_);
v___y_3370_ = v___x_3394_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3395_; lean_object* v_localDeclNameView_3396_; uint8_t v___x_3397_; 
lean_dec(v_fullDeclName_3392_);
v___x_3395_ = l_Lean_LocalDecl_userName(v_val_3373_);
v_localDeclNameView_3396_ = l_Lean_extractMacroScopes(v___x_3395_);
v___x_3397_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3396_, v_givenNameView_3361_);
lean_dec_ref(v_localDeclNameView_3396_);
if (v___x_3397_ == 0)
{
lean_dec_ref(v_fullDeclView_3391_);
v_i_3363_ = v_n_3368_;
goto _start;
}
else
{
uint8_t v___x_3399_; 
v___x_3399_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3361_, v_fullDeclView_3391_);
lean_dec_ref(v_fullDeclView_3391_);
if (v___x_3399_ == 0)
{
v_i_3363_ = v_n_3368_;
goto _start;
}
else
{
lean_inc_ref(v___x_3372_);
v___y_3370_ = v___x_3372_;
goto v___jp_3369_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3407_; 
lean_dec(v___x_3379_);
lean_inc(v_val_3373_);
v___x_3407_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3373_, v_givenName_3357_);
v___y_3370_ = v___x_3407_;
goto v___jp_3369_;
}
}
}
}
v___jp_3369_:
{
if (lean_obj_tag(v___y_3370_) == 0)
{
v_i_3363_ = v_n_3368_;
goto _start;
}
else
{
lean_dec(v_n_3368_);
lean_dec_ref(v_givenNameView_3361_);
lean_dec(v___x_3360_);
return v___y_3370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3408_, lean_object* v_skipAuxDecl_3409_, lean_object* v_auxDeclToFullName_3410_, lean_object* v___x_3411_, lean_object* v_givenNameView_3412_, lean_object* v_as_3413_, lean_object* v_i_3414_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3415_; lean_object* v_res_3416_; 
v_skipAuxDecl_boxed_3415_ = lean_unbox(v_skipAuxDecl_3409_);
v_res_3416_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3408_, v_skipAuxDecl_boxed_3415_, v_auxDeclToFullName_3410_, v___x_3411_, v_givenNameView_3412_, v_as_3413_, v_i_3414_);
lean_dec_ref(v_as_3413_);
lean_dec(v_auxDeclToFullName_3410_);
lean_dec(v_givenName_3408_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3417_, uint8_t v_skipAuxDecl_3418_, lean_object* v_auxDeclToFullName_3419_, lean_object* v___x_3420_, lean_object* v_givenNameView_3421_, lean_object* v_as_3422_, lean_object* v_i_3423_){
_start:
{
lean_object* v_zero_3424_; uint8_t v_isZero_3425_; 
v_zero_3424_ = lean_unsigned_to_nat(0u);
v_isZero_3425_ = lean_nat_dec_eq(v_i_3423_, v_zero_3424_);
if (v_isZero_3425_ == 1)
{
lean_object* v___x_3426_; 
lean_dec(v_i_3423_);
lean_dec_ref(v_givenNameView_3421_);
lean_dec(v___x_3420_);
v___x_3426_ = lean_box(0);
return v___x_3426_;
}
else
{
lean_object* v_one_3427_; lean_object* v_n_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_one_3427_ = lean_unsigned_to_nat(1u);
v_n_3428_ = lean_nat_sub(v_i_3423_, v_one_3427_);
lean_dec(v_i_3423_);
v___x_3429_ = lean_array_fget_borrowed(v_as_3422_, v_n_3428_);
lean_inc_ref(v_givenNameView_3421_);
lean_inc(v___x_3420_);
v___x_3430_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3417_, v_skipAuxDecl_3418_, v_auxDeclToFullName_3419_, v___x_3420_, v_givenNameView_3421_, v___x_3429_);
if (lean_obj_tag(v___x_3430_) == 0)
{
v_i_3423_ = v_n_3428_;
goto _start;
}
else
{
lean_dec(v_n_3428_);
lean_dec_ref(v_givenNameView_3421_);
lean_dec(v___x_3420_);
return v___x_3430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3432_, uint8_t v_skipAuxDecl_3433_, lean_object* v_auxDeclToFullName_3434_, lean_object* v___x_3435_, lean_object* v_givenNameView_3436_, lean_object* v_x_3437_){
_start:
{
if (lean_obj_tag(v_x_3437_) == 0)
{
lean_object* v_cs_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v_cs_3438_ = lean_ctor_get(v_x_3437_, 0);
v___x_3439_ = lean_array_get_size(v_cs_3438_);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3432_, v_skipAuxDecl_3433_, v_auxDeclToFullName_3434_, v___x_3435_, v_givenNameView_3436_, v_cs_3438_, v___x_3439_);
return v___x_3440_;
}
else
{
lean_object* v_vs_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v_vs_3441_ = lean_ctor_get(v_x_3437_, 0);
v___x_3442_ = lean_array_get_size(v_vs_3441_);
v___x_3443_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3432_, v_skipAuxDecl_3433_, v_auxDeclToFullName_3434_, v___x_3435_, v_givenNameView_3436_, v_vs_3441_, v___x_3442_);
return v___x_3443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3444_, lean_object* v_skipAuxDecl_3445_, lean_object* v_auxDeclToFullName_3446_, lean_object* v___x_3447_, lean_object* v_givenNameView_3448_, lean_object* v_x_3449_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3450_; lean_object* v_res_3451_; 
v_skipAuxDecl_boxed_3450_ = lean_unbox(v_skipAuxDecl_3445_);
v_res_3451_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3444_, v_skipAuxDecl_boxed_3450_, v_auxDeclToFullName_3446_, v___x_3447_, v_givenNameView_3448_, v_x_3449_);
lean_dec_ref(v_x_3449_);
lean_dec(v_auxDeclToFullName_3446_);
lean_dec(v_givenName_3444_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3452_, lean_object* v_skipAuxDecl_3453_, lean_object* v_auxDeclToFullName_3454_, lean_object* v___x_3455_, lean_object* v_givenNameView_3456_, lean_object* v_as_3457_, lean_object* v_i_3458_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3459_; lean_object* v_res_3460_; 
v_skipAuxDecl_boxed_3459_ = lean_unbox(v_skipAuxDecl_3453_);
v_res_3460_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3452_, v_skipAuxDecl_boxed_3459_, v_auxDeclToFullName_3454_, v___x_3455_, v_givenNameView_3456_, v_as_3457_, v_i_3458_);
lean_dec_ref(v_as_3457_);
lean_dec(v_auxDeclToFullName_3454_);
lean_dec(v_givenName_3452_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3461_, uint8_t v_skipAuxDecl_3462_, lean_object* v_auxDeclToFullName_3463_, lean_object* v___x_3464_, lean_object* v_givenNameView_3465_, lean_object* v_t_3466_){
_start:
{
lean_object* v_root_3467_; lean_object* v_tail_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_root_3467_ = lean_ctor_get(v_t_3466_, 0);
v_tail_3468_ = lean_ctor_get(v_t_3466_, 1);
v___x_3469_ = lean_array_get_size(v_tail_3468_);
lean_inc_ref(v_givenNameView_3465_);
lean_inc(v___x_3464_);
v___x_3470_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3461_, v_skipAuxDecl_3462_, v_auxDeclToFullName_3463_, v___x_3464_, v_givenNameView_3465_, v_tail_3468_, v___x_3469_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3461_, v_skipAuxDecl_3462_, v_auxDeclToFullName_3463_, v___x_3464_, v_givenNameView_3465_, v_root_3467_);
return v___x_3471_;
}
else
{
lean_dec_ref(v_givenNameView_3465_);
lean_dec(v___x_3464_);
return v___x_3470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3472_, lean_object* v_skipAuxDecl_3473_, lean_object* v_auxDeclToFullName_3474_, lean_object* v___x_3475_, lean_object* v_givenNameView_3476_, lean_object* v_t_3477_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3478_; lean_object* v_res_3479_; 
v_skipAuxDecl_boxed_3478_ = lean_unbox(v_skipAuxDecl_3473_);
v_res_3479_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3472_, v_skipAuxDecl_boxed_3478_, v_auxDeclToFullName_3474_, v___x_3475_, v_givenNameView_3476_, v_t_3477_);
lean_dec_ref(v_t_3477_);
lean_dec(v_auxDeclToFullName_3474_);
lean_dec(v_givenName_3472_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3480_, lean_object* v_currNamespace_3481_, lean_object* v_decls_3482_, lean_object* v_givenNameView_3483_, uint8_t v_skipAuxDecl_3484_){
_start:
{
lean_object* v_givenName_3485_; lean_object* v_localDecl_x3f_3486_; 
lean_inc_ref(v_givenNameView_3483_);
v_givenName_3485_ = l_Lean_MacroScopesView_review(v_givenNameView_3483_);
v_localDecl_x3f_3486_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3485_, v_skipAuxDecl_3484_, v_auxDeclToFullName_3480_, v_currNamespace_3481_, v_givenNameView_3483_, v_decls_3482_);
if (lean_obj_tag(v_localDecl_x3f_3486_) == 0)
{
if (v_skipAuxDecl_3484_ == 0)
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3486_, v_givenName_3485_, v_decls_3482_);
lean_dec(v_givenName_3485_);
return v___x_3487_;
}
else
{
lean_dec(v_givenName_3485_);
return v_localDecl_x3f_3486_;
}
}
else
{
lean_dec(v_givenName_3485_);
return v_localDecl_x3f_3486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3488_, lean_object* v_currNamespace_3489_, lean_object* v_decls_3490_, lean_object* v_givenNameView_3491_, lean_object* v_skipAuxDecl_3492_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3493_; lean_object* v_res_3494_; 
v_skipAuxDecl_boxed_3493_ = lean_unbox(v_skipAuxDecl_3492_);
v_res_3494_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3488_, v_currNamespace_3489_, v_decls_3490_, v_givenNameView_3491_, v_skipAuxDecl_boxed_3493_);
lean_dec_ref(v_decls_3490_);
lean_dec(v_auxDeclToFullName_3488_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v_lctx_3503_; lean_object* v_decls_3504_; lean_object* v_auxDeclToFullName_3505_; lean_object* v_currNamespace_3506_; lean_object* v_view_3507_; lean_object* v_name_3508_; lean_object* v_findLocalDecl_x3f_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; lean_object* v___x_3512_; 
v_lctx_3503_ = lean_ctor_get(v___y_3498_, 2);
v_decls_3504_ = lean_ctor_get(v_lctx_3503_, 1);
v_auxDeclToFullName_3505_ = lean_ctor_get(v_lctx_3503_, 2);
v_currNamespace_3506_ = lean_ctor_get(v___y_3500_, 6);
v_view_3507_ = l_Lean_extractMacroScopes(v_n_3495_);
v_name_3508_ = lean_ctor_get(v_view_3507_, 0);
lean_inc(v_name_3508_);
lean_inc_ref(v_decls_3504_);
lean_inc(v_currNamespace_3506_);
lean_inc(v_auxDeclToFullName_3505_);
v_findLocalDecl_x3f_3509_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3509_, 0, v_auxDeclToFullName_3505_);
lean_closure_set(v_findLocalDecl_x3f_3509_, 1, v_currNamespace_3506_);
lean_closure_set(v_findLocalDecl_x3f_3509_, 2, v_decls_3504_);
v___x_3510_ = lean_box(0);
v___x_3511_ = 0;
v___x_3512_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3507_, v_findLocalDecl_x3f_3509_, v_name_3508_, v___x_3510_, v___x_3511_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec_ref(v_view_3507_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3522_, lean_object* v_b_3523_){
_start:
{
if (lean_obj_tag(v_as_x27_3522_) == 0)
{
lean_object* v___x_3525_; 
v___x_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_b_3523_);
return v___x_3525_;
}
else
{
lean_object* v_head_3526_; lean_object* v_tail_3527_; lean_object* v_config_3528_; lean_object* v_extensions_3529_; lean_object* v_extra_3530_; lean_object* v_extraInj_3531_; lean_object* v_extraFacts_3532_; lean_object* v_symPrios_3533_; lean_object* v_norm_3534_; lean_object* v_normProcs_3535_; lean_object* v_anchorRefs_x3f_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3545_; 
v_head_3526_ = lean_ctor_get(v_as_x27_3522_, 0);
v_tail_3527_ = lean_ctor_get(v_as_x27_3522_, 1);
v_config_3528_ = lean_ctor_get(v_b_3523_, 0);
v_extensions_3529_ = lean_ctor_get(v_b_3523_, 1);
v_extra_3530_ = lean_ctor_get(v_b_3523_, 2);
v_extraInj_3531_ = lean_ctor_get(v_b_3523_, 3);
v_extraFacts_3532_ = lean_ctor_get(v_b_3523_, 4);
v_symPrios_3533_ = lean_ctor_get(v_b_3523_, 5);
v_norm_3534_ = lean_ctor_get(v_b_3523_, 6);
v_normProcs_3535_ = lean_ctor_get(v_b_3523_, 7);
v_anchorRefs_x3f_3536_ = lean_ctor_get(v_b_3523_, 8);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_b_3523_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3538_ = v_b_3523_;
v_isShared_3539_ = v_isSharedCheck_3545_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_anchorRefs_x3f_3536_);
lean_inc(v_normProcs_3535_);
lean_inc(v_norm_3534_);
lean_inc(v_symPrios_3533_);
lean_inc(v_extraFacts_3532_);
lean_inc(v_extraInj_3531_);
lean_inc(v_extra_3530_);
lean_inc(v_extensions_3529_);
lean_inc(v_config_3528_);
lean_dec(v_b_3523_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3545_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; lean_object* v___x_3542_; 
lean_inc(v_head_3526_);
v___x_3540_ = l_Lean_PersistentArray_push___redArg(v_extra_3530_, v_head_3526_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 2, v___x_3540_);
v___x_3542_ = v___x_3538_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_config_3528_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v_extensions_3529_);
lean_ctor_set(v_reuseFailAlloc_3544_, 2, v___x_3540_);
lean_ctor_set(v_reuseFailAlloc_3544_, 3, v_extraInj_3531_);
lean_ctor_set(v_reuseFailAlloc_3544_, 4, v_extraFacts_3532_);
lean_ctor_set(v_reuseFailAlloc_3544_, 5, v_symPrios_3533_);
lean_ctor_set(v_reuseFailAlloc_3544_, 6, v_norm_3534_);
lean_ctor_set(v_reuseFailAlloc_3544_, 7, v_normProcs_3535_);
lean_ctor_set(v_reuseFailAlloc_3544_, 8, v_anchorRefs_x3f_3536_);
v___x_3542_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
v_as_x27_3522_ = v_tail_3527_;
v_b_3523_ = v___x_3542_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3546_, lean_object* v_b_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3546_, v_b_3547_);
lean_dec(v_as_x27_3546_);
return v_res_3549_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3552_ = l_Lean_stringToMessageData(v___x_3551_);
return v___x_3552_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3555_ = l_Lean_stringToMessageData(v___x_3554_);
return v___x_3555_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3558_ = l_Lean_stringToMessageData(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3561_ = l_Lean_stringToMessageData(v___x_3560_);
return v___x_3561_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3564_ = l_Lean_stringToMessageData(v___x_3563_);
return v___x_3564_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3567_ = l_Lean_stringToMessageData(v___x_3566_);
return v___x_3567_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3570_ = l_Lean_stringToMessageData(v___x_3569_);
return v___x_3570_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3573_ = l_Lean_stringToMessageData(v___x_3572_);
return v___x_3573_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3576_ = l_Lean_stringToMessageData(v___x_3575_);
return v___x_3576_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3579_ = l_Lean_stringToMessageData(v___x_3578_);
return v___x_3579_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3582_ = l_Lean_stringToMessageData(v___x_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3583_, lean_object* v_p_3584_, lean_object* v_mod_x3f_3585_, lean_object* v_id_3586_, uint8_t v_minIndexable_3587_, uint8_t v_only_3588_, uint8_t v_incremental_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3710_; uint8_t v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v_a_3772_; lean_object* v___y_3997_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = lean_box(0);
lean_inc(v_id_3586_);
v___x_4009_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3586_, v___x_4008_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4009_, 1);
v_a_3772_ = v_a_4010_;
goto v___jp_3771_;
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4086_; 
v_a_4011_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4013_ = v___x_4009_;
v_isShared_4014_ = v_isSharedCheck_4086_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4009_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4086_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
uint8_t v___y_4016_; uint8_t v___x_4084_; 
v___x_4084_ = l_Lean_Exception_isInterrupt(v_a_4011_);
if (v___x_4084_ == 0)
{
uint8_t v___x_4085_; 
lean_inc(v_a_4011_);
v___x_4085_ = l_Lean_Exception_isRuntime(v_a_4011_);
v___y_4016_ = v___x_4085_;
goto v___jp_4015_;
}
else
{
v___y_4016_ = v___x_4084_;
goto v___jp_4015_;
}
v___jp_4015_:
{
if (v___y_4016_ == 0)
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_del_object(v___x_4013_);
v___x_4017_ = l_Lean_TSyntax_getId(v_id_3586_);
lean_inc(v___x_4017_);
v___x_4018_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4017_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_a_4019_);
lean_dec_ref_known(v___x_4018_, 1);
if (lean_obj_tag(v_a_4019_) == 0)
{
lean_object* v___x_4020_; 
v___x_4020_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4017_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4050_; 
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4023_ = v___x_4020_;
v_isShared_4024_ = v_isSharedCheck_4050_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4020_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4050_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
if (lean_obj_tag(v_a_4021_) == 1)
{
lean_del_object(v___x_4023_);
lean_dec(v_a_4011_);
if (lean_obj_tag(v_mod_x3f_3585_) == 1)
{
lean_object* v_val_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_dec_ref_known(v_a_4021_, 1);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_val_4025_ = lean_ctor_get(v_mod_x3f_3585_, 0);
lean_inc(v_val_4025_);
lean_dec_ref_known(v_mod_x3f_3585_, 1);
v___x_4026_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_4027_ = l_Lean_MessageData_ofName(v___x_4017_);
v___x_4028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4026_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
v___x_4029_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4028_);
lean_ctor_set(v___x_4030_, 1, v___x_4029_);
v___x_4031_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4025_, v___x_4030_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
lean_dec(v_val_4025_);
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_4031_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4031_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
else
{
lean_object* v_val_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_dec(v___x_4017_);
v_val_4040_ = lean_ctor_get(v_a_4021_, 0);
lean_inc(v_val_4040_);
lean_dec_ref_known(v_a_4021_, 1);
v___x_4041_ = lean_box(0);
lean_inc_ref(v_params_3583_);
v___x_4042_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3583_, v_val_4040_, v___x_4041_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
lean_dec(v_val_4040_);
v___y_3997_ = v___x_4042_;
goto v___jp_3996_;
}
}
else
{
lean_object* v___x_4043_; uint8_t v___x_4044_; uint8_t v___x_4045_; 
lean_dec(v_a_4021_);
v___x_4043_ = l_Lean_Name_getPrefix(v___x_4017_);
lean_dec(v___x_4017_);
v___x_4044_ = l_Lean_Name_isAnonymous(v___x_4043_);
lean_dec(v___x_4043_);
v___x_4045_ = lean_bool_not(v___x_4044_);
if (v___x_4045_ == 0)
{
lean_object* v___x_4047_; 
lean_dec(v_id_3586_);
lean_dec(v_mod_x3f_3585_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
if (v_isShared_4024_ == 0)
{
lean_ctor_set_tag(v___x_4023_, 1);
lean_ctor_set(v___x_4023_, 0, v_a_4011_);
v___x_4047_ = v___x_4023_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4011_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
else
{
lean_object* v___x_4049_; 
lean_del_object(v___x_4023_);
lean_dec(v_a_4011_);
v___x_4049_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3583_, v_p_3584_, v_mod_x3f_3585_, v_id_3586_, v_minIndexable_3587_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
return v___x_4049_;
}
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec(v___x_4017_);
lean_dec(v_a_4011_);
lean_dec(v_id_3586_);
lean_dec(v_mod_x3f_3585_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_a_4051_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4020_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4020_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
else
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref_known(v_a_4019_, 1);
lean_dec(v___x_4017_);
lean_dec(v_a_4011_);
lean_dec(v_mod_x3f_3585_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v___x_4059_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
lean_inc(v_id_3586_);
v___x_4060_ = l_Lean_MessageData_ofSyntax(v_id_3586_);
v___x_4061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4059_);
lean_ctor_set(v___x_4061_, 1, v___x_4060_);
v___x_4062_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4061_);
lean_ctor_set(v___x_4063_, 1, v___x_4062_);
v___x_4064_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3586_, v___x_4063_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
lean_dec(v_id_3586_);
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4064_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4064_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v___x_4017_);
lean_dec(v_a_4011_);
lean_dec(v_id_3586_);
lean_dec(v_mod_x3f_3585_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_a_4073_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4018_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4018_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v___x_4082_; 
lean_dec(v_id_3586_);
lean_dec(v_mod_x3f_3585_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
if (v_isShared_4014_ == 0)
{
v___x_4082_ = v___x_4013_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4011_);
v___x_4082_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
return v___x_4082_;
}
}
}
}
}
v___jp_3597_:
{
uint8_t v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = 0;
lean_inc(v___y_3598_);
v___x_3606_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3598_, v___x_3605_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
if (lean_obj_tag(v_a_3607_) == 1)
{
lean_object* v_val_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
lean_dec(v___y_3598_);
v_val_3608_ = lean_ctor_get(v_a_3607_, 0);
lean_inc_n(v_val_3608_, 2);
lean_dec_ref_known(v_a_3607_, 1);
v___x_3609_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3583_, v_val_3608_, v___x_3605_);
v___x_3610_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3608_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3621_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3621_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3621_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
if (lean_obj_tag(v_a_3611_) == 1)
{
lean_object* v_val_3615_; lean_object* v_ctors_3616_; lean_object* v___x_3617_; 
lean_del_object(v___x_3613_);
v_val_3615_ = lean_ctor_get(v_a_3611_, 0);
lean_inc(v_val_3615_);
lean_dec_ref_known(v_a_3611_, 1);
v_ctors_3616_ = lean_ctor_get(v_val_3615_, 4);
lean_inc(v_ctors_3616_);
lean_dec(v_val_3615_);
v___x_3617_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3584_, v_id_3586_, v_minIndexable_3587_, v_ctors_3616_, v___x_3609_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
lean_dec(v_ctors_3616_);
lean_dec(v_p_3584_);
return v___x_3617_;
}
else
{
lean_object* v___x_3619_; 
lean_dec(v_a_3611_);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v___x_3609_);
v___x_3619_ = v___x_3613_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3609_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec_ref(v___x_3609_);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
v_a_3622_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3610_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3610_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
else
{
lean_object* v_fileName_3630_; lean_object* v_fileMap_3631_; lean_object* v_options_3632_; lean_object* v_currRecDepth_3633_; lean_object* v_maxRecDepth_3634_; lean_object* v_ref_3635_; lean_object* v_currNamespace_3636_; lean_object* v_openDecls_3637_; lean_object* v_initHeartbeats_3638_; lean_object* v_maxHeartbeats_3639_; lean_object* v_quotContext_3640_; lean_object* v_currMacroScope_3641_; uint8_t v_diag_3642_; lean_object* v_cancelTk_x3f_3643_; uint8_t v_suppressElabErrors_3644_; lean_object* v_inheritedTraceOptions_3645_; lean_object* v___x_3646_; uint8_t v___x_3647_; lean_object* v_ref_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
lean_dec(v_a_3607_);
v_fileName_3630_ = lean_ctor_get(v___y_3603_, 0);
v_fileMap_3631_ = lean_ctor_get(v___y_3603_, 1);
v_options_3632_ = lean_ctor_get(v___y_3603_, 2);
v_currRecDepth_3633_ = lean_ctor_get(v___y_3603_, 3);
v_maxRecDepth_3634_ = lean_ctor_get(v___y_3603_, 4);
v_ref_3635_ = lean_ctor_get(v___y_3603_, 5);
v_currNamespace_3636_ = lean_ctor_get(v___y_3603_, 6);
v_openDecls_3637_ = lean_ctor_get(v___y_3603_, 7);
v_initHeartbeats_3638_ = lean_ctor_get(v___y_3603_, 8);
v_maxHeartbeats_3639_ = lean_ctor_get(v___y_3603_, 9);
v_quotContext_3640_ = lean_ctor_get(v___y_3603_, 10);
v_currMacroScope_3641_ = lean_ctor_get(v___y_3603_, 11);
v_diag_3642_ = lean_ctor_get_uint8(v___y_3603_, sizeof(void*)*14);
v_cancelTk_x3f_3643_ = lean_ctor_get(v___y_3603_, 12);
v_suppressElabErrors_3644_ = lean_ctor_get_uint8(v___y_3603_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3645_ = lean_ctor_get(v___y_3603_, 13);
v___x_3646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_3647_ = 1;
v_ref_3648_ = l_Lean_replaceRef(v_p_3584_, v_ref_3635_);
lean_dec(v_p_3584_);
lean_inc_ref(v_inheritedTraceOptions_3645_);
lean_inc(v_cancelTk_x3f_3643_);
lean_inc(v_currMacroScope_3641_);
lean_inc(v_quotContext_3640_);
lean_inc(v_maxHeartbeats_3639_);
lean_inc(v_initHeartbeats_3638_);
lean_inc(v_openDecls_3637_);
lean_inc(v_currNamespace_3636_);
lean_inc(v_maxRecDepth_3634_);
lean_inc(v_currRecDepth_3633_);
lean_inc_ref(v_options_3632_);
lean_inc_ref(v_fileMap_3631_);
lean_inc_ref(v_fileName_3630_);
v___x_3649_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3649_, 0, v_fileName_3630_);
lean_ctor_set(v___x_3649_, 1, v_fileMap_3631_);
lean_ctor_set(v___x_3649_, 2, v_options_3632_);
lean_ctor_set(v___x_3649_, 3, v_currRecDepth_3633_);
lean_ctor_set(v___x_3649_, 4, v_maxRecDepth_3634_);
lean_ctor_set(v___x_3649_, 5, v_ref_3648_);
lean_ctor_set(v___x_3649_, 6, v_currNamespace_3636_);
lean_ctor_set(v___x_3649_, 7, v_openDecls_3637_);
lean_ctor_set(v___x_3649_, 8, v_initHeartbeats_3638_);
lean_ctor_set(v___x_3649_, 9, v_maxHeartbeats_3639_);
lean_ctor_set(v___x_3649_, 10, v_quotContext_3640_);
lean_ctor_set(v___x_3649_, 11, v_currMacroScope_3641_);
lean_ctor_set(v___x_3649_, 12, v_cancelTk_x3f_3643_);
lean_ctor_set(v___x_3649_, 13, v_inheritedTraceOptions_3645_);
lean_ctor_set_uint8(v___x_3649_, sizeof(void*)*14, v_diag_3642_);
lean_ctor_set_uint8(v___x_3649_, sizeof(void*)*14 + 1, v_suppressElabErrors_3644_);
v___x_3650_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3583_, v_id_3586_, v___y_3598_, v___x_3646_, v_minIndexable_3587_, v___x_3647_, v___x_3647_, v___y_3601_, v___y_3602_, v___x_3649_, v___y_3604_);
lean_dec_ref_known(v___x_3649_, 14);
return v___x_3650_;
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
lean_dec(v___y_3598_);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_a_3651_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3606_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3606_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
v___jp_3659_:
{
lean_object* v___x_3668_; 
v___x_3668_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3587_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
lean_dec_ref_known(v___x_3668_, 1);
v___x_3669_ = l_Lean_Meta_Grind_grindExt;
v___x_3670_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3669_, v___y_3667_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref_known(v___x_3670_, 1);
lean_inc(v___y_3661_);
v___x_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3672_, 0, v___y_3661_);
v___x_3673_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3671_, v___x_3672_);
lean_dec_ref_known(v___x_3672_, 1);
lean_dec(v_a_3671_);
v___x_3674_ = lean_box(0);
v___x_3675_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3660_, v___x_3673_, v___x_3674_);
lean_dec(v___y_3660_);
v___x_3676_ = l_List_isEmpty___redArg(v___x_3675_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; 
lean_dec(v___y_3661_);
lean_dec(v_p_3584_);
v___x_3677_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3675_, v_params_3583_);
lean_dec(v___x_3675_);
return v___x_3677_;
}
else
{
lean_object* v___x_3678_; uint8_t v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec(v___x_3675_);
lean_dec_ref(v_params_3583_);
v___x_3678_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3679_ = 0;
v___x_3680_ = l_Lean_MessageData_ofConstName(v___y_3661_, v___x_3679_);
v___x_3681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3678_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3681_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3584_, v___x_3683_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
lean_dec(v_p_3584_);
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3684_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_dec(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_a_3693_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3670_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3670_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_a_3701_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3668_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3668_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
v___jp_3709_:
{
lean_object* v___x_3716_; 
v___x_3716_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3587_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_fileName_3717_; lean_object* v_fileMap_3718_; lean_object* v_options_3719_; lean_object* v_currRecDepth_3720_; lean_object* v_maxRecDepth_3721_; lean_object* v_ref_3722_; lean_object* v_currNamespace_3723_; lean_object* v_openDecls_3724_; lean_object* v_initHeartbeats_3725_; lean_object* v_maxHeartbeats_3726_; lean_object* v_quotContext_3727_; lean_object* v_currMacroScope_3728_; uint8_t v_diag_3729_; lean_object* v_cancelTk_x3f_3730_; uint8_t v_suppressElabErrors_3731_; lean_object* v_inheritedTraceOptions_3732_; lean_object* v_ref_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
lean_dec_ref_known(v___x_3716_, 1);
v_fileName_3717_ = lean_ctor_get(v___y_3714_, 0);
v_fileMap_3718_ = lean_ctor_get(v___y_3714_, 1);
v_options_3719_ = lean_ctor_get(v___y_3714_, 2);
v_currRecDepth_3720_ = lean_ctor_get(v___y_3714_, 3);
v_maxRecDepth_3721_ = lean_ctor_get(v___y_3714_, 4);
v_ref_3722_ = lean_ctor_get(v___y_3714_, 5);
v_currNamespace_3723_ = lean_ctor_get(v___y_3714_, 6);
v_openDecls_3724_ = lean_ctor_get(v___y_3714_, 7);
v_initHeartbeats_3725_ = lean_ctor_get(v___y_3714_, 8);
v_maxHeartbeats_3726_ = lean_ctor_get(v___y_3714_, 9);
v_quotContext_3727_ = lean_ctor_get(v___y_3714_, 10);
v_currMacroScope_3728_ = lean_ctor_get(v___y_3714_, 11);
v_diag_3729_ = lean_ctor_get_uint8(v___y_3714_, sizeof(void*)*14);
v_cancelTk_x3f_3730_ = lean_ctor_get(v___y_3714_, 12);
v_suppressElabErrors_3731_ = lean_ctor_get_uint8(v___y_3714_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3732_ = lean_ctor_get(v___y_3714_, 13);
v_ref_3733_ = l_Lean_replaceRef(v_p_3584_, v_ref_3722_);
lean_dec(v_p_3584_);
lean_inc_ref(v_inheritedTraceOptions_3732_);
lean_inc(v_cancelTk_x3f_3730_);
lean_inc(v_currMacroScope_3728_);
lean_inc(v_quotContext_3727_);
lean_inc(v_maxHeartbeats_3726_);
lean_inc(v_initHeartbeats_3725_);
lean_inc(v_openDecls_3724_);
lean_inc(v_currNamespace_3723_);
lean_inc(v_maxRecDepth_3721_);
lean_inc(v_currRecDepth_3720_);
lean_inc_ref(v_options_3719_);
lean_inc_ref(v_fileMap_3718_);
lean_inc_ref(v_fileName_3717_);
v___x_3734_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3734_, 0, v_fileName_3717_);
lean_ctor_set(v___x_3734_, 1, v_fileMap_3718_);
lean_ctor_set(v___x_3734_, 2, v_options_3719_);
lean_ctor_set(v___x_3734_, 3, v_currRecDepth_3720_);
lean_ctor_set(v___x_3734_, 4, v_maxRecDepth_3721_);
lean_ctor_set(v___x_3734_, 5, v_ref_3733_);
lean_ctor_set(v___x_3734_, 6, v_currNamespace_3723_);
lean_ctor_set(v___x_3734_, 7, v_openDecls_3724_);
lean_ctor_set(v___x_3734_, 8, v_initHeartbeats_3725_);
lean_ctor_set(v___x_3734_, 9, v_maxHeartbeats_3726_);
lean_ctor_set(v___x_3734_, 10, v_quotContext_3727_);
lean_ctor_set(v___x_3734_, 11, v_currMacroScope_3728_);
lean_ctor_set(v___x_3734_, 12, v_cancelTk_x3f_3730_);
lean_ctor_set(v___x_3734_, 13, v_inheritedTraceOptions_3732_);
lean_ctor_set_uint8(v___x_3734_, sizeof(void*)*14, v_diag_3729_);
lean_ctor_set_uint8(v___x_3734_, sizeof(void*)*14 + 1, v_suppressElabErrors_3731_);
lean_inc(v___y_3710_);
v___x_3735_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3710_, v___y_3711_, v___x_3734_, v___y_3715_);
lean_dec_ref_known(v___x_3734_, 14);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3743_; 
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3743_ == 0)
{
lean_object* v_unused_3744_; 
v_unused_3744_ = lean_ctor_get(v___x_3735_, 0);
lean_dec(v_unused_3744_);
v___x_3737_ = v___x_3735_;
v_isShared_3738_ = v_isSharedCheck_3743_;
goto v_resetjp_3736_;
}
else
{
lean_dec(v___x_3735_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3743_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3739_; lean_object* v___x_3741_; 
v___x_3739_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3583_, v___y_3710_, v___y_3711_);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v___x_3739_);
v___x_3741_ = v___x_3737_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec(v___y_3710_);
lean_dec_ref(v_params_3583_);
v_a_3745_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3735_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3735_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_dec(v___y_3710_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_a_3753_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3716_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3716_);
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
v___jp_3761_:
{
lean_object* v_ctors_3769_; lean_object* v___x_3770_; 
v_ctors_3769_ = lean_ctor_get(v___y_3762_, 4);
lean_inc(v_ctors_3769_);
lean_dec_ref(v___y_3762_);
v___x_3770_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3584_, v_id_3586_, v_minIndexable_3587_, v_ctors_3769_, v_params_3583_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
lean_dec(v_ctors_3769_);
lean_dec(v_p_3584_);
return v___x_3770_;
}
v___jp_3771_:
{
lean_object* v___x_3773_; 
lean_inc(v_a_3772_);
v___x_3773_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_3772_, v_a_3590_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_dec_ref_known(v___x_3773_, 1);
if (lean_obj_tag(v_mod_x3f_3585_) == 1)
{
lean_object* v_val_3774_; lean_object* v___x_3775_; 
v_val_3774_ = lean_ctor_get(v_mod_x3f_3585_, 0);
lean_inc(v_val_3774_);
lean_dec_ref_known(v_mod_x3f_3585_, 1);
v___x_3775_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3774_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3979_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3979_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3979_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
switch(lean_obj_tag(v_a_3776_))
{
case 0:
{
lean_object* v_k_3780_; 
lean_del_object(v___x_3778_);
v_k_3780_ = lean_ctor_get(v_a_3776_, 0);
lean_inc(v_k_3780_);
lean_dec_ref_known(v_a_3776_, 1);
if (lean_obj_tag(v_k_3780_) == 9)
{
lean_dec(v_id_3586_);
if (v_only_3588_ == 0)
{
lean_object* v_fileName_3781_; lean_object* v_fileMap_3782_; lean_object* v_options_3783_; lean_object* v_currRecDepth_3784_; lean_object* v_maxRecDepth_3785_; lean_object* v_ref_3786_; lean_object* v_currNamespace_3787_; lean_object* v_openDecls_3788_; lean_object* v_initHeartbeats_3789_; lean_object* v_maxHeartbeats_3790_; lean_object* v_quotContext_3791_; lean_object* v_currMacroScope_3792_; uint8_t v_diag_3793_; lean_object* v_cancelTk_x3f_3794_; uint8_t v_suppressElabErrors_3795_; lean_object* v_inheritedTraceOptions_3796_; lean_object* v_ref_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v_fileName_3781_ = lean_ctor_get(v_a_3594_, 0);
v_fileMap_3782_ = lean_ctor_get(v_a_3594_, 1);
v_options_3783_ = lean_ctor_get(v_a_3594_, 2);
v_currRecDepth_3784_ = lean_ctor_get(v_a_3594_, 3);
v_maxRecDepth_3785_ = lean_ctor_get(v_a_3594_, 4);
v_ref_3786_ = lean_ctor_get(v_a_3594_, 5);
v_currNamespace_3787_ = lean_ctor_get(v_a_3594_, 6);
v_openDecls_3788_ = lean_ctor_get(v_a_3594_, 7);
v_initHeartbeats_3789_ = lean_ctor_get(v_a_3594_, 8);
v_maxHeartbeats_3790_ = lean_ctor_get(v_a_3594_, 9);
v_quotContext_3791_ = lean_ctor_get(v_a_3594_, 10);
v_currMacroScope_3792_ = lean_ctor_get(v_a_3594_, 11);
v_diag_3793_ = lean_ctor_get_uint8(v_a_3594_, sizeof(void*)*14);
v_cancelTk_x3f_3794_ = lean_ctor_get(v_a_3594_, 12);
v_suppressElabErrors_3795_ = lean_ctor_get_uint8(v_a_3594_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3796_ = lean_ctor_get(v_a_3594_, 13);
v_ref_3797_ = l_Lean_replaceRef(v_p_3584_, v_ref_3786_);
lean_inc_ref(v_inheritedTraceOptions_3796_);
lean_inc(v_cancelTk_x3f_3794_);
lean_inc(v_currMacroScope_3792_);
lean_inc(v_quotContext_3791_);
lean_inc(v_maxHeartbeats_3790_);
lean_inc(v_initHeartbeats_3789_);
lean_inc(v_openDecls_3788_);
lean_inc(v_currNamespace_3787_);
lean_inc(v_maxRecDepth_3785_);
lean_inc(v_currRecDepth_3784_);
lean_inc_ref(v_options_3783_);
lean_inc_ref(v_fileMap_3782_);
lean_inc_ref(v_fileName_3781_);
v___x_3798_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3798_, 0, v_fileName_3781_);
lean_ctor_set(v___x_3798_, 1, v_fileMap_3782_);
lean_ctor_set(v___x_3798_, 2, v_options_3783_);
lean_ctor_set(v___x_3798_, 3, v_currRecDepth_3784_);
lean_ctor_set(v___x_3798_, 4, v_maxRecDepth_3785_);
lean_ctor_set(v___x_3798_, 5, v_ref_3797_);
lean_ctor_set(v___x_3798_, 6, v_currNamespace_3787_);
lean_ctor_set(v___x_3798_, 7, v_openDecls_3788_);
lean_ctor_set(v___x_3798_, 8, v_initHeartbeats_3789_);
lean_ctor_set(v___x_3798_, 9, v_maxHeartbeats_3790_);
lean_ctor_set(v___x_3798_, 10, v_quotContext_3791_);
lean_ctor_set(v___x_3798_, 11, v_currMacroScope_3792_);
lean_ctor_set(v___x_3798_, 12, v_cancelTk_x3f_3794_);
lean_ctor_set(v___x_3798_, 13, v_inheritedTraceOptions_3796_);
lean_ctor_set_uint8(v___x_3798_, sizeof(void*)*14, v_diag_3793_);
lean_ctor_set_uint8(v___x_3798_, sizeof(void*)*14 + 1, v_suppressElabErrors_3795_);
v___x_3799_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_3798_, v_a_3595_);
lean_dec_ref_known(v___x_3798_, 14);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_dec_ref_known(v___x_3799_, 1);
v___y_3660_ = v_k_3780_;
v___y_3661_ = v_a_3772_;
v___y_3662_ = v_a_3590_;
v___y_3663_ = v_a_3591_;
v___y_3664_ = v_a_3592_;
v___y_3665_ = v_a_3593_;
v___y_3666_ = v_a_3594_;
v___y_3667_ = v_a_3595_;
goto v___jp_3659_;
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec(v_a_3772_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3799_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
else
{
v___y_3660_ = v_k_3780_;
v___y_3661_ = v_a_3772_;
v___y_3662_ = v_a_3590_;
v___y_3663_ = v_a_3591_;
v___y_3664_ = v_a_3592_;
v___y_3665_ = v_a_3593_;
v___y_3666_ = v_a_3594_;
v___y_3667_ = v_a_3595_;
goto v___jp_3659_;
}
}
else
{
lean_object* v_fileName_3808_; lean_object* v_fileMap_3809_; lean_object* v_options_3810_; lean_object* v_currRecDepth_3811_; lean_object* v_maxRecDepth_3812_; lean_object* v_ref_3813_; lean_object* v_currNamespace_3814_; lean_object* v_openDecls_3815_; lean_object* v_initHeartbeats_3816_; lean_object* v_maxHeartbeats_3817_; lean_object* v_quotContext_3818_; lean_object* v_currMacroScope_3819_; uint8_t v_diag_3820_; lean_object* v_cancelTk_x3f_3821_; uint8_t v_suppressElabErrors_3822_; lean_object* v_inheritedTraceOptions_3823_; uint8_t v___x_3824_; uint8_t v___x_3825_; lean_object* v_ref_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v_fileName_3808_ = lean_ctor_get(v_a_3594_, 0);
v_fileMap_3809_ = lean_ctor_get(v_a_3594_, 1);
v_options_3810_ = lean_ctor_get(v_a_3594_, 2);
v_currRecDepth_3811_ = lean_ctor_get(v_a_3594_, 3);
v_maxRecDepth_3812_ = lean_ctor_get(v_a_3594_, 4);
v_ref_3813_ = lean_ctor_get(v_a_3594_, 5);
v_currNamespace_3814_ = lean_ctor_get(v_a_3594_, 6);
v_openDecls_3815_ = lean_ctor_get(v_a_3594_, 7);
v_initHeartbeats_3816_ = lean_ctor_get(v_a_3594_, 8);
v_maxHeartbeats_3817_ = lean_ctor_get(v_a_3594_, 9);
v_quotContext_3818_ = lean_ctor_get(v_a_3594_, 10);
v_currMacroScope_3819_ = lean_ctor_get(v_a_3594_, 11);
v_diag_3820_ = lean_ctor_get_uint8(v_a_3594_, sizeof(void*)*14);
v_cancelTk_x3f_3821_ = lean_ctor_get(v_a_3594_, 12);
v_suppressElabErrors_3822_ = lean_ctor_get_uint8(v_a_3594_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3823_ = lean_ctor_get(v_a_3594_, 13);
v___x_3824_ = 0;
v___x_3825_ = 1;
v_ref_3826_ = l_Lean_replaceRef(v_p_3584_, v_ref_3813_);
lean_dec(v_p_3584_);
lean_inc_ref(v_inheritedTraceOptions_3823_);
lean_inc(v_cancelTk_x3f_3821_);
lean_inc(v_currMacroScope_3819_);
lean_inc(v_quotContext_3818_);
lean_inc(v_maxHeartbeats_3817_);
lean_inc(v_initHeartbeats_3816_);
lean_inc(v_openDecls_3815_);
lean_inc(v_currNamespace_3814_);
lean_inc(v_maxRecDepth_3812_);
lean_inc(v_currRecDepth_3811_);
lean_inc_ref(v_options_3810_);
lean_inc_ref(v_fileMap_3809_);
lean_inc_ref(v_fileName_3808_);
v___x_3827_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3827_, 0, v_fileName_3808_);
lean_ctor_set(v___x_3827_, 1, v_fileMap_3809_);
lean_ctor_set(v___x_3827_, 2, v_options_3810_);
lean_ctor_set(v___x_3827_, 3, v_currRecDepth_3811_);
lean_ctor_set(v___x_3827_, 4, v_maxRecDepth_3812_);
lean_ctor_set(v___x_3827_, 5, v_ref_3826_);
lean_ctor_set(v___x_3827_, 6, v_currNamespace_3814_);
lean_ctor_set(v___x_3827_, 7, v_openDecls_3815_);
lean_ctor_set(v___x_3827_, 8, v_initHeartbeats_3816_);
lean_ctor_set(v___x_3827_, 9, v_maxHeartbeats_3817_);
lean_ctor_set(v___x_3827_, 10, v_quotContext_3818_);
lean_ctor_set(v___x_3827_, 11, v_currMacroScope_3819_);
lean_ctor_set(v___x_3827_, 12, v_cancelTk_x3f_3821_);
lean_ctor_set(v___x_3827_, 13, v_inheritedTraceOptions_3823_);
lean_ctor_set_uint8(v___x_3827_, sizeof(void*)*14, v_diag_3820_);
lean_ctor_set_uint8(v___x_3827_, sizeof(void*)*14 + 1, v_suppressElabErrors_3822_);
v___x_3828_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3583_, v_id_3586_, v_a_3772_, v_k_3780_, v_minIndexable_3587_, v___x_3824_, v___x_3825_, v_a_3592_, v_a_3593_, v___x_3827_, v_a_3595_);
lean_dec_ref_known(v___x_3827_, 14);
return v___x_3828_;
}
}
case 1:
{
lean_del_object(v___x_3778_);
lean_dec(v_id_3586_);
if (v_incremental_3589_ == 0)
{
uint8_t v_eager_3829_; 
v_eager_3829_ = lean_ctor_get_uint8(v_a_3776_, 0);
lean_dec_ref_known(v_a_3776_, 0);
v___y_3710_ = v_a_3772_;
v___y_3711_ = v_eager_3829_;
v___y_3712_ = v_a_3592_;
v___y_3713_ = v_a_3593_;
v___y_3714_ = v_a_3594_;
v___y_3715_ = v_a_3595_;
goto v___jp_3709_;
}
else
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec_ref_known(v_a_3776_, 0);
lean_dec(v_a_3772_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v___x_3830_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3831_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3830_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
case 2:
{
uint8_t v___x_3840_; lean_object* v___x_3841_; 
lean_del_object(v___x_3778_);
v___x_3840_ = 0;
lean_inc(v_a_3772_);
v___x_3841_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3772_, v___x_3840_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v___x_3841_, 1);
if (lean_obj_tag(v_a_3842_) == 1)
{
lean_dec(v_a_3772_);
if (v_incremental_3589_ == 0)
{
lean_object* v_val_3843_; 
v_val_3843_ = lean_ctor_get(v_a_3842_, 0);
lean_inc(v_val_3843_);
lean_dec_ref_known(v_a_3842_, 1);
v___y_3762_ = v_val_3843_;
v___y_3763_ = v_a_3590_;
v___y_3764_ = v_a_3591_;
v___y_3765_ = v_a_3592_;
v___y_3766_ = v_a_3593_;
v___y_3767_ = v_a_3594_;
v___y_3768_ = v_a_3595_;
goto v___jp_3761_;
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_dec_ref_known(v_a_3842_, 1);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v___x_3844_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3845_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3844_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3845_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3845_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
else
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_a_3842_);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v___x_3854_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_3855_ = l_Lean_MessageData_ofConstName(v_a_3772_, v___x_3840_);
v___x_3856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3854_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
v___x_3857_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3858_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3859_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3859_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec(v_a_3772_);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_a_3868_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3841_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3841_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
case 3:
{
lean_del_object(v___x_3778_);
v___y_3598_ = v_a_3772_;
v___y_3599_ = v_a_3590_;
v___y_3600_ = v_a_3591_;
v___y_3601_ = v_a_3592_;
v___y_3602_ = v_a_3593_;
v___y_3603_ = v_a_3594_;
v___y_3604_ = v_a_3595_;
goto v___jp_3597_;
}
case 4:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_del_object(v___x_3778_);
lean_dec(v_a_3772_);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v___x_3876_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_3877_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3876_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
case 5:
{
lean_object* v_prio_3886_; lean_object* v___x_3887_; 
lean_del_object(v___x_3778_);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
v_prio_3886_ = lean_ctor_get(v_a_3776_, 0);
lean_inc(v_prio_3886_);
lean_dec_ref_known(v_a_3776_, 1);
v___x_3887_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3587_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3911_; 
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; 
v_unused_3912_ = lean_ctor_get(v___x_3887_, 0);
lean_dec(v_unused_3912_);
v___x_3889_ = v___x_3887_;
v_isShared_3890_ = v_isSharedCheck_3911_;
goto v_resetjp_3888_;
}
else
{
lean_dec(v___x_3887_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3911_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v_config_3891_; lean_object* v_extensions_3892_; lean_object* v_extra_3893_; lean_object* v_extraInj_3894_; lean_object* v_extraFacts_3895_; lean_object* v_symPrios_3896_; lean_object* v_norm_3897_; lean_object* v_normProcs_3898_; lean_object* v_anchorRefs_x3f_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3910_; 
v_config_3891_ = lean_ctor_get(v_params_3583_, 0);
v_extensions_3892_ = lean_ctor_get(v_params_3583_, 1);
v_extra_3893_ = lean_ctor_get(v_params_3583_, 2);
v_extraInj_3894_ = lean_ctor_get(v_params_3583_, 3);
v_extraFacts_3895_ = lean_ctor_get(v_params_3583_, 4);
v_symPrios_3896_ = lean_ctor_get(v_params_3583_, 5);
v_norm_3897_ = lean_ctor_get(v_params_3583_, 6);
v_normProcs_3898_ = lean_ctor_get(v_params_3583_, 7);
v_anchorRefs_x3f_3899_ = lean_ctor_get(v_params_3583_, 8);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_params_3583_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3901_ = v_params_3583_;
v_isShared_3902_ = v_isSharedCheck_3910_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_anchorRefs_x3f_3899_);
lean_inc(v_normProcs_3898_);
lean_inc(v_norm_3897_);
lean_inc(v_symPrios_3896_);
lean_inc(v_extraFacts_3895_);
lean_inc(v_extraInj_3894_);
lean_inc(v_extra_3893_);
lean_inc(v_extensions_3892_);
lean_inc(v_config_3891_);
lean_dec(v_params_3583_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3910_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3903_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_3896_, v_a_3772_, v_prio_3886_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 5, v___x_3903_);
v___x_3905_ = v___x_3901_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_config_3891_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_extensions_3892_);
lean_ctor_set(v_reuseFailAlloc_3909_, 2, v_extra_3893_);
lean_ctor_set(v_reuseFailAlloc_3909_, 3, v_extraInj_3894_);
lean_ctor_set(v_reuseFailAlloc_3909_, 4, v_extraFacts_3895_);
lean_ctor_set(v_reuseFailAlloc_3909_, 5, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3909_, 6, v_norm_3897_);
lean_ctor_set(v_reuseFailAlloc_3909_, 7, v_normProcs_3898_);
lean_ctor_set(v_reuseFailAlloc_3909_, 8, v_anchorRefs_x3f_3899_);
v___x_3905_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3907_; 
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v___x_3905_);
v___x_3907_ = v___x_3889_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec(v_prio_3886_);
lean_dec(v_a_3772_);
lean_dec_ref(v_params_3583_);
v_a_3913_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3887_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3887_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
case 6:
{
lean_object* v___x_3921_; 
lean_del_object(v___x_3778_);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
v___x_3921_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3772_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3946_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3924_ = v___x_3921_;
v_isShared_3925_ = v_isSharedCheck_3946_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3921_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3946_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v_config_3926_; lean_object* v_extensions_3927_; lean_object* v_extra_3928_; lean_object* v_extraInj_3929_; lean_object* v_extraFacts_3930_; lean_object* v_symPrios_3931_; lean_object* v_norm_3932_; lean_object* v_normProcs_3933_; lean_object* v_anchorRefs_x3f_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3945_; 
v_config_3926_ = lean_ctor_get(v_params_3583_, 0);
v_extensions_3927_ = lean_ctor_get(v_params_3583_, 1);
v_extra_3928_ = lean_ctor_get(v_params_3583_, 2);
v_extraInj_3929_ = lean_ctor_get(v_params_3583_, 3);
v_extraFacts_3930_ = lean_ctor_get(v_params_3583_, 4);
v_symPrios_3931_ = lean_ctor_get(v_params_3583_, 5);
v_norm_3932_ = lean_ctor_get(v_params_3583_, 6);
v_normProcs_3933_ = lean_ctor_get(v_params_3583_, 7);
v_anchorRefs_x3f_3934_ = lean_ctor_get(v_params_3583_, 8);
v_isSharedCheck_3945_ = !lean_is_exclusive(v_params_3583_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3936_ = v_params_3583_;
v_isShared_3937_ = v_isSharedCheck_3945_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_anchorRefs_x3f_3934_);
lean_inc(v_normProcs_3933_);
lean_inc(v_norm_3932_);
lean_inc(v_symPrios_3931_);
lean_inc(v_extraFacts_3930_);
lean_inc(v_extraInj_3929_);
lean_inc(v_extra_3928_);
lean_inc(v_extensions_3927_);
lean_inc(v_config_3926_);
lean_dec(v_params_3583_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3945_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3938_; lean_object* v___x_3940_; 
v___x_3938_ = l_Lean_PersistentArray_push___redArg(v_extraInj_3929_, v_a_3922_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 3, v___x_3938_);
v___x_3940_ = v___x_3936_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_config_3926_);
lean_ctor_set(v_reuseFailAlloc_3944_, 1, v_extensions_3927_);
lean_ctor_set(v_reuseFailAlloc_3944_, 2, v_extra_3928_);
lean_ctor_set(v_reuseFailAlloc_3944_, 3, v___x_3938_);
lean_ctor_set(v_reuseFailAlloc_3944_, 4, v_extraFacts_3930_);
lean_ctor_set(v_reuseFailAlloc_3944_, 5, v_symPrios_3931_);
lean_ctor_set(v_reuseFailAlloc_3944_, 6, v_norm_3932_);
lean_ctor_set(v_reuseFailAlloc_3944_, 7, v_normProcs_3933_);
lean_ctor_set(v_reuseFailAlloc_3944_, 8, v_anchorRefs_x3f_3934_);
v___x_3940_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
lean_object* v___x_3942_; 
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 0, v___x_3940_);
v___x_3942_ = v___x_3924_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec_ref(v_params_3583_);
v_a_3947_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3921_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3921_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
case 7:
{
lean_object* v___x_3955_; lean_object* v___x_3957_; 
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
v___x_3955_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3583_, v_a_3772_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 0, v___x_3955_);
v___x_3957_ = v___x_3778_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3955_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
case 8:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
lean_dec_ref_known(v_a_3776_, 0);
lean_del_object(v___x_3778_);
lean_dec(v_a_3772_);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v___x_3959_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_3960_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3959_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3963_ = v___x_3960_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3960_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
default: 
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_del_object(v___x_3778_);
lean_dec(v_a_3772_);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v___x_3969_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_3970_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3969_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3970_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec(v_a_3772_);
lean_dec(v_id_3586_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_a_3980_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3775_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3775_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3585_);
v___y_3598_ = v_a_3772_;
v___y_3599_ = v_a_3590_;
v___y_3600_ = v_a_3591_;
v___y_3601_ = v_a_3592_;
v___y_3602_ = v_a_3593_;
v___y_3603_ = v_a_3594_;
v___y_3604_ = v_a_3595_;
goto v___jp_3597_;
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec(v_a_3772_);
lean_dec(v_id_3586_);
lean_dec(v_mod_x3f_3585_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_a_3988_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3773_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3773_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
v___jp_3996_:
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4007_; 
v_a_3998_ = lean_ctor_get(v___y_3997_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___y_3997_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4000_ = v___y_3997_;
v_isShared_4001_ = v_isSharedCheck_4007_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___y_3997_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4007_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
if (lean_obj_tag(v_a_3998_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4004_; 
lean_dec(v_id_3586_);
lean_dec(v_mod_x3f_3585_);
lean_dec(v_p_3584_);
lean_dec_ref(v_params_3583_);
v_a_4002_ = lean_ctor_get(v_a_3998_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v_a_3998_, 1);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 0, v_a_4002_);
v___x_4004_ = v___x_4000_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_4002_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
else
{
lean_object* v_a_4006_; 
lean_del_object(v___x_4000_);
v_a_4006_ = lean_ctor_get(v_a_3998_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v_a_3998_, 1);
v_a_3772_ = v_a_4006_;
goto v___jp_3771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4087_, lean_object* v_p_4088_, lean_object* v_mod_x3f_4089_, lean_object* v_id_4090_, lean_object* v_minIndexable_4091_, lean_object* v_only_4092_, lean_object* v_incremental_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
uint8_t v_minIndexable_boxed_4101_; uint8_t v_only_boxed_4102_; uint8_t v_incremental_boxed_4103_; lean_object* v_res_4104_; 
v_minIndexable_boxed_4101_ = lean_unbox(v_minIndexable_4091_);
v_only_boxed_4102_ = lean_unbox(v_only_4092_);
v_incremental_boxed_4103_ = lean_unbox(v_incremental_4093_);
v_res_4104_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4087_, v_p_4088_, v_mod_x3f_4089_, v_id_4090_, v_minIndexable_boxed_4101_, v_only_boxed_4102_, v_incremental_boxed_4103_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
lean_dec(v_a_4099_);
lean_dec_ref(v_a_4098_);
lean_dec(v_a_4097_);
lean_dec_ref(v_a_4096_);
lean_dec(v_a_4095_);
lean_dec_ref(v_a_4094_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4105_, lean_object* v_id_4106_, uint8_t v_minIndexable_4107_, lean_object* v_as_4108_, lean_object* v_as_x27_4109_, lean_object* v_b_4110_, lean_object* v_a_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4105_, v_id_4106_, v_minIndexable_4107_, v_as_x27_4109_, v_b_4110_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4120_, lean_object* v_id_4121_, lean_object* v_minIndexable_4122_, lean_object* v_as_4123_, lean_object* v_as_x27_4124_, lean_object* v_b_4125_, lean_object* v_a_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
uint8_t v_minIndexable_boxed_4134_; lean_object* v_res_4135_; 
v_minIndexable_boxed_4134_ = lean_unbox(v_minIndexable_4122_);
v_res_4135_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4120_, v_id_4121_, v_minIndexable_boxed_4134_, v_as_4123_, v_as_x27_4124_, v_b_4125_, v_a_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v_as_x27_4124_);
lean_dec(v_as_4123_);
lean_dec(v_p_4120_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4136_, lean_object* v_as_x27_4137_, lean_object* v_b_4138_, lean_object* v_a_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v___x_4147_; 
v___x_4147_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4137_, v_b_4138_);
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4148_, lean_object* v_as_x27_4149_, lean_object* v_b_4150_, lean_object* v_a_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4148_, v_as_x27_4149_, v_b_4150_, v_a_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v_as_x27_4149_);
lean_dec(v_as_4148_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4160_, lean_object* v_ref_4161_, lean_object* v_msg_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v___x_4170_; 
v___x_4170_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4161_, v_msg_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4171_, lean_object* v_ref_4172_, lean_object* v_msg_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4171_, v_ref_4172_, v_msg_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v_ref_4172_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4182_, lean_object* v_id_4183_, uint8_t v_minIndexable_4184_, lean_object* v_as_4185_, lean_object* v_as_x27_4186_, lean_object* v_b_4187_, lean_object* v_a_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4182_, v_id_4183_, v_minIndexable_4184_, v_as_x27_4186_, v_b_4187_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4197_, lean_object* v_id_4198_, lean_object* v_minIndexable_4199_, lean_object* v_as_4200_, lean_object* v_as_x27_4201_, lean_object* v_b_4202_, lean_object* v_a_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
uint8_t v_minIndexable_boxed_4211_; lean_object* v_res_4212_; 
v_minIndexable_boxed_4211_ = lean_unbox(v_minIndexable_4199_);
v_res_4212_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4197_, v_id_4198_, v_minIndexable_boxed_4211_, v_as_4200_, v_as_x27_4201_, v_b_4202_, v_a_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v_as_x27_4201_);
lean_dec(v_as_4200_);
lean_dec(v_p_4197_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4213_, lean_object* v_t_4214_, lean_object* v_k_4215_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4214_, v_k_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4217_, lean_object* v_t_4218_, lean_object* v_k_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4217_, v_t_4218_, v_k_4219_);
lean_dec(v_k_4219_);
lean_dec(v_t_4218_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4221_, uint8_t v_skipAuxDecl_4222_, lean_object* v_auxDeclToFullName_4223_, lean_object* v___x_4224_, lean_object* v_givenNameView_4225_, lean_object* v_as_4226_, lean_object* v_i_4227_, lean_object* v_a_4228_){
_start:
{
lean_object* v___x_4229_; 
v___x_4229_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4221_, v_skipAuxDecl_4222_, v_auxDeclToFullName_4223_, v___x_4224_, v_givenNameView_4225_, v_as_4226_, v_i_4227_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4230_, lean_object* v_skipAuxDecl_4231_, lean_object* v_auxDeclToFullName_4232_, lean_object* v___x_4233_, lean_object* v_givenNameView_4234_, lean_object* v_as_4235_, lean_object* v_i_4236_, lean_object* v_a_4237_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4238_; lean_object* v_res_4239_; 
v_skipAuxDecl_boxed_4238_ = lean_unbox(v_skipAuxDecl_4231_);
v_res_4239_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4230_, v_skipAuxDecl_boxed_4238_, v_auxDeclToFullName_4232_, v___x_4233_, v_givenNameView_4234_, v_as_4235_, v_i_4236_, v_a_4237_);
lean_dec_ref(v_as_4235_);
lean_dec(v_auxDeclToFullName_4232_);
lean_dec(v_givenName_4230_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4240_, lean_object* v_givenName_4241_, lean_object* v_as_4242_, lean_object* v_i_4243_, lean_object* v_a_4244_){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4240_, v_givenName_4241_, v_as_4242_, v_i_4243_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4246_, lean_object* v_givenName_4247_, lean_object* v_as_4248_, lean_object* v_i_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4246_, v_givenName_4247_, v_as_4248_, v_i_4249_, v_a_4250_);
lean_dec_ref(v_as_4248_);
lean_dec(v_givenName_4247_);
lean_dec(v_localDecl_x3f_4246_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4252_, uint8_t v_skipAuxDecl_4253_, lean_object* v_auxDeclToFullName_4254_, lean_object* v___x_4255_, lean_object* v_givenNameView_4256_, lean_object* v_as_4257_, lean_object* v_i_4258_, lean_object* v_a_4259_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4252_, v_skipAuxDecl_4253_, v_auxDeclToFullName_4254_, v___x_4255_, v_givenNameView_4256_, v_as_4257_, v_i_4258_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4261_, lean_object* v_skipAuxDecl_4262_, lean_object* v_auxDeclToFullName_4263_, lean_object* v___x_4264_, lean_object* v_givenNameView_4265_, lean_object* v_as_4266_, lean_object* v_i_4267_, lean_object* v_a_4268_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4269_; lean_object* v_res_4270_; 
v_skipAuxDecl_boxed_4269_ = lean_unbox(v_skipAuxDecl_4262_);
v_res_4270_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4261_, v_skipAuxDecl_boxed_4269_, v_auxDeclToFullName_4263_, v___x_4264_, v_givenNameView_4265_, v_as_4266_, v_i_4267_, v_a_4268_);
lean_dec_ref(v_as_4266_);
lean_dec(v_auxDeclToFullName_4263_);
lean_dec(v_givenName_4261_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4271_, lean_object* v_givenName_4272_, lean_object* v_as_4273_, lean_object* v_i_4274_, lean_object* v_a_4275_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4271_, v_givenName_4272_, v_as_4273_, v_i_4274_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4277_, lean_object* v_givenName_4278_, lean_object* v_as_4279_, lean_object* v_i_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4277_, v_givenName_4278_, v_as_4279_, v_i_4280_, v_a_4281_);
lean_dec_ref(v_as_4279_);
lean_dec(v_givenName_4278_);
lean_dec(v_localDecl_x3f_4277_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4283_, v___y_4288_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec_ref(v_opt_4292_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4301_, lean_object* v_msgData_4302_, uint8_t v_severity_4303_, uint8_t v_isSilent_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4301_, v_msgData_4302_, v_severity_4303_, v_isSilent_4304_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4313_, lean_object* v_msgData_4314_, lean_object* v_severity_4315_, lean_object* v_isSilent_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
uint8_t v_severity_boxed_4324_; uint8_t v_isSilent_boxed_4325_; lean_object* v_res_4326_; 
v_severity_boxed_4324_ = lean_unbox(v_severity_4315_);
v_isSilent_boxed_4325_ = lean_unbox(v_isSilent_4316_);
v_res_4326_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4313_, v_msgData_4314_, v_severity_boxed_4324_, v_isSilent_boxed_4325_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v_ref_4313_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4327_, lean_object* v_b_4328_, lean_object* v_____r_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = lean_box(0);
v___x_4338_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4327_, v___x_4337_, v___y_4334_, v___y_4335_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; lean_object* v___x_4340_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc_n(v_a_4339_, 2);
lean_dec_ref_known(v___x_4338_, 1);
v___x_4340_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4339_, v___y_4330_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
if (lean_obj_tag(v___x_4340_) == 0)
{
uint8_t v___x_4341_; lean_object* v___x_4342_; 
lean_dec_ref_known(v___x_4340_, 1);
v___x_4341_ = 0;
lean_inc(v_a_4339_);
v___x_4342_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4339_, v___x_4341_, v___y_4334_, v___y_4335_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4402_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4345_ = v___x_4342_;
v_isShared_4346_ = v_isSharedCheck_4402_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4342_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4402_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
if (lean_obj_tag(v_a_4343_) == 1)
{
lean_object* v_val_4347_; lean_object* v___x_4348_; 
lean_del_object(v___x_4345_);
lean_dec(v_a_4339_);
v_val_4347_ = lean_ctor_get(v_a_4343_, 0);
lean_inc_n(v_val_4347_, 2);
lean_dec_ref_known(v_a_4343_, 1);
v___x_4348_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4347_, v___y_4334_, v___y_4335_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v___x_4349_; 
lean_dec_ref_known(v___x_4348_, 1);
v___x_4349_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4328_, v_val_4347_, v___y_4334_, v___y_4335_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4359_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4352_ = v___x_4349_;
v_isShared_4353_ = v_isSharedCheck_4359_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4349_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4359_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4354_ = lean_box(0);
v___x_4355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4354_);
lean_ctor_set(v___x_4355_, 1, v_a_4350_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v___x_4355_);
v___x_4357_ = v___x_4352_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4355_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
v_a_4360_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4349_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4349_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
lean_dec(v_val_4347_);
lean_dec_ref(v_b_4328_);
v_a_4368_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4348_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4348_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
else
{
uint8_t v___x_4376_; 
lean_dec(v_a_4343_);
lean_inc(v_a_4339_);
v___x_4376_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4328_, v_a_4339_);
if (v___x_4376_ == 0)
{
lean_object* v___x_4377_; 
lean_del_object(v___x_4345_);
v___x_4377_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4328_, v_a_4339_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4387_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4380_ = v___x_4377_;
v_isShared_4381_ = v_isSharedCheck_4387_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4377_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4387_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4385_; 
v___x_4382_ = lean_box(0);
v___x_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4382_);
lean_ctor_set(v___x_4383_, 1, v_a_4378_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 0, v___x_4383_);
v___x_4385_ = v___x_4380_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
v_a_4388_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4377_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4377_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
else
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4396_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4328_, v_a_4339_);
v___x_4397_ = lean_box(0);
v___x_4398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4397_);
lean_ctor_set(v___x_4398_, 1, v___x_4396_);
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 0, v___x_4398_);
v___x_4400_ = v___x_4345_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4398_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_a_4339_);
lean_dec_ref(v_b_4328_);
v_a_4403_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4342_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4342_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_a_4339_);
lean_dec_ref(v_b_4328_);
v_a_4411_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4340_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4340_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec_ref(v_b_4328_);
v_a_4419_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4338_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4338_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4427_, lean_object* v_b_4428_, lean_object* v_____r_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4427_, v_b_4428_, v_____r_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4441_, lean_object* v_b_4442_, lean_object* v_a_4443_, uint8_t v___x_4444_, uint8_t v_only_4445_, uint8_t v_incremental_4446_, lean_object* v_x_4447_, lean_object* v_mod_x3f_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; uint8_t v___x_4459_; 
v___x_4456_ = lean_unsigned_to_nat(1u);
v___x_4457_ = l_Lean_Syntax_getArg(v___x_4441_, v___x_4456_);
v___x_4458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4457_);
v___x_4459_ = l_Lean_Syntax_isOfKind(v___x_4457_, v___x_4458_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4460_; 
v___x_4460_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4442_, v_a_4443_, v_mod_x3f_4448_, v___x_4457_, v___x_4459_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4470_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4463_ = v___x_4460_;
v_isShared_4464_ = v_isSharedCheck_4470_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4460_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4470_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4468_; 
v___x_4465_ = lean_box(0);
v___x_4466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4465_);
lean_ctor_set(v___x_4466_, 1, v_a_4461_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4466_);
v___x_4468_ = v___x_4463_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
else
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
v_a_4471_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4473_ = v___x_4460_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4460_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
else
{
lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4479_ = l_Lean_TSyntax_getId(v___x_4457_);
v___x_4480_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4479_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4481_);
lean_dec_ref_known(v___x_4480_, 1);
if (lean_obj_tag(v_a_4481_) == 1)
{
lean_object* v_val_4508_; lean_object* v_snd_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4534_; 
v_val_4508_ = lean_ctor_get(v_a_4481_, 0);
lean_inc(v_val_4508_);
lean_dec_ref_known(v_a_4481_, 1);
v_snd_4509_ = lean_ctor_get(v_val_4508_, 1);
v_isSharedCheck_4534_ = !lean_is_exclusive(v_val_4508_);
if (v_isSharedCheck_4534_ == 0)
{
lean_object* v_unused_4535_; 
v_unused_4535_ = lean_ctor_get(v_val_4508_, 0);
lean_dec(v_unused_4535_);
v___x_4511_ = v_val_4508_;
v_isShared_4512_ = v_isSharedCheck_4534_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_snd_4509_);
lean_dec(v_val_4508_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4534_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
if (lean_obj_tag(v_snd_4509_) == 1)
{
lean_object* v___x_4513_; 
lean_dec_ref_known(v_snd_4509_, 2);
v___x_4513_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4442_, v_a_4443_, v_mod_x3f_4448_, v___x_4457_, v___x_4444_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4525_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4516_ = v___x_4513_;
v_isShared_4517_ = v_isSharedCheck_4525_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4513_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4525_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4518_; lean_object* v___x_4520_; 
v___x_4518_ = lean_box(0);
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 1, v_a_4514_);
lean_ctor_set(v___x_4511_, 0, v___x_4518_);
v___x_4520_ = v___x_4511_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v___x_4518_);
lean_ctor_set(v_reuseFailAlloc_4524_, 1, v_a_4514_);
v___x_4520_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
lean_object* v___x_4522_; 
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 0, v___x_4520_);
v___x_4522_ = v___x_4516_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4520_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_del_object(v___x_4511_);
v_a_4526_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4513_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4513_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
else
{
lean_del_object(v___x_4511_);
lean_dec(v_snd_4509_);
v___y_4483_ = v___y_4449_;
v___y_4484_ = v___y_4450_;
v___y_4485_ = v___y_4451_;
v___y_4486_ = v___y_4452_;
v___y_4487_ = v___y_4453_;
v___y_4488_ = v___y_4454_;
goto v___jp_4482_;
}
}
}
else
{
lean_dec(v_a_4481_);
v___y_4483_ = v___y_4449_;
v___y_4484_ = v___y_4450_;
v___y_4485_ = v___y_4451_;
v___y_4486_ = v___y_4452_;
v___y_4487_ = v___y_4453_;
v___y_4488_ = v___y_4454_;
goto v___jp_4482_;
}
v___jp_4482_:
{
lean_object* v___x_4489_; 
v___x_4489_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4442_, v_a_4443_, v_mod_x3f_4448_, v___x_4457_, v___x_4444_, v_only_4445_, v_incremental_4446_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4499_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4492_ = v___x_4489_;
v_isShared_4493_ = v_isSharedCheck_4499_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4489_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4499_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4497_; 
v___x_4494_ = lean_box(0);
v___x_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
lean_ctor_set(v___x_4495_, 1, v_a_4490_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 0, v___x_4495_);
v___x_4497_ = v___x_4492_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4495_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
v_a_4500_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4489_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4489_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_dec(v___x_4457_);
lean_dec(v_mod_x3f_4448_);
lean_dec(v_a_4443_);
lean_dec_ref(v_b_4442_);
v_a_4536_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4480_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4480_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4544_, lean_object* v_b_4545_, lean_object* v_a_4546_, lean_object* v___x_4547_, lean_object* v_only_4548_, lean_object* v_incremental_4549_, lean_object* v_x_4550_, lean_object* v_mod_x3f_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
uint8_t v___x_23832__boxed_4559_; uint8_t v_only_boxed_4560_; uint8_t v_incremental_boxed_4561_; lean_object* v_res_4562_; 
v___x_23832__boxed_4559_ = lean_unbox(v___x_4547_);
v_only_boxed_4560_ = lean_unbox(v_only_4548_);
v_incremental_boxed_4561_ = lean_unbox(v_incremental_4549_);
v_res_4562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4544_, v_b_4545_, v_a_4546_, v___x_23832__boxed_4559_, v_only_boxed_4560_, v_incremental_boxed_4561_, v_x_4550_, v_mod_x3f_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v___x_4544_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4563_, lean_object* v___x_4564_, lean_object* v_____r_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v___x_4573_; 
v___x_4573_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4563_, v___x_4564_, v___y_4570_, v___y_4571_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4583_; 
v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4576_ = v___x_4573_;
v_isShared_4577_ = v_isSharedCheck_4583_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4573_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4583_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4581_; 
v___x_4578_ = lean_box(0);
v___x_4579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
lean_ctor_set(v___x_4579_, 1, v_a_4574_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v___x_4579_);
v___x_4581_ = v___x_4576_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4579_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
v_a_4584_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4573_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4573_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4592_, lean_object* v___x_4593_, lean_object* v_____r_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4592_, v___x_4593_, v_____r_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec(v___x_4593_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4603_, lean_object* v_b_4604_, lean_object* v_a_4605_, uint8_t v___x_4606_, uint8_t v_only_4607_, uint8_t v_incremental_4608_, lean_object* v_x_4609_, lean_object* v_mod_x3f_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; uint8_t v___x_4621_; 
v___x_4618_ = lean_unsigned_to_nat(2u);
v___x_4619_ = l_Lean_Syntax_getArg(v___x_4603_, v___x_4618_);
v___x_4620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4619_);
v___x_4621_ = l_Lean_Syntax_isOfKind(v___x_4619_, v___x_4620_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; 
v___x_4622_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4604_, v_a_4605_, v_mod_x3f_4610_, v___x_4619_, v___x_4606_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4632_; 
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4625_ = v___x_4622_;
v_isShared_4626_ = v_isSharedCheck_4632_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4622_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4632_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4630_; 
v___x_4627_ = lean_box(0);
v___x_4628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4627_);
lean_ctor_set(v___x_4628_, 1, v_a_4623_);
if (v_isShared_4626_ == 0)
{
lean_ctor_set(v___x_4625_, 0, v___x_4628_);
v___x_4630_ = v___x_4625_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4628_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4640_; 
v_a_4633_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4635_ = v___x_4622_;
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4622_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4636_ == 0)
{
v___x_4638_ = v___x_4635_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
else
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = l_Lean_TSyntax_getId(v___x_4619_);
v___x_4642_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4641_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v___y_4650_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_a_4643_);
lean_dec_ref_known(v___x_4642_, 1);
if (lean_obj_tag(v_a_4643_) == 1)
{
lean_object* v_val_4670_; lean_object* v_snd_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4696_; 
v_val_4670_ = lean_ctor_get(v_a_4643_, 0);
lean_inc(v_val_4670_);
lean_dec_ref_known(v_a_4643_, 1);
v_snd_4671_ = lean_ctor_get(v_val_4670_, 1);
v_isSharedCheck_4696_ = !lean_is_exclusive(v_val_4670_);
if (v_isSharedCheck_4696_ == 0)
{
lean_object* v_unused_4697_; 
v_unused_4697_ = lean_ctor_get(v_val_4670_, 0);
lean_dec(v_unused_4697_);
v___x_4673_ = v_val_4670_;
v_isShared_4674_ = v_isSharedCheck_4696_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_snd_4671_);
lean_dec(v_val_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4696_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
if (lean_obj_tag(v_snd_4671_) == 1)
{
lean_object* v___x_4675_; 
lean_dec_ref_known(v_snd_4671_, 2);
v___x_4675_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4604_, v_a_4605_, v_mod_x3f_4610_, v___x_4619_, v___x_4606_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4687_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4678_ = v___x_4675_;
v_isShared_4679_ = v_isSharedCheck_4687_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4675_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4687_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4680_; lean_object* v___x_4682_; 
v___x_4680_ = lean_box(0);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 1, v_a_4676_);
lean_ctor_set(v___x_4673_, 0, v___x_4680_);
v___x_4682_ = v___x_4673_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4680_);
lean_ctor_set(v_reuseFailAlloc_4686_, 1, v_a_4676_);
v___x_4682_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4684_; 
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 0, v___x_4682_);
v___x_4684_ = v___x_4678_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
else
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4695_; 
lean_del_object(v___x_4673_);
v_a_4688_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4690_ = v___x_4675_;
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4675_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4693_; 
if (v_isShared_4691_ == 0)
{
v___x_4693_ = v___x_4690_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4688_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
}
else
{
lean_del_object(v___x_4673_);
lean_dec(v_snd_4671_);
v___y_4645_ = v___y_4611_;
v___y_4646_ = v___y_4612_;
v___y_4647_ = v___y_4613_;
v___y_4648_ = v___y_4614_;
v___y_4649_ = v___y_4615_;
v___y_4650_ = v___y_4616_;
goto v___jp_4644_;
}
}
}
else
{
lean_dec(v_a_4643_);
v___y_4645_ = v___y_4611_;
v___y_4646_ = v___y_4612_;
v___y_4647_ = v___y_4613_;
v___y_4648_ = v___y_4614_;
v___y_4649_ = v___y_4615_;
v___y_4650_ = v___y_4616_;
goto v___jp_4644_;
}
v___jp_4644_:
{
lean_object* v___x_4651_; 
v___x_4651_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4604_, v_a_4605_, v_mod_x3f_4610_, v___x_4619_, v___x_4606_, v_only_4607_, v_incremental_4608_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4661_; 
v_a_4652_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4654_ = v___x_4651_;
v_isShared_4655_ = v_isSharedCheck_4661_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4651_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4661_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4659_; 
v___x_4656_ = lean_box(0);
v___x_4657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
lean_ctor_set(v___x_4657_, 1, v_a_4652_);
if (v_isShared_4655_ == 0)
{
lean_ctor_set(v___x_4654_, 0, v___x_4657_);
v___x_4659_ = v___x_4654_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4657_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
v_a_4662_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4651_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4651_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
}
else
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4705_; 
lean_dec(v___x_4619_);
lean_dec(v_mod_x3f_4610_);
lean_dec(v_a_4605_);
lean_dec_ref(v_b_4604_);
v_a_4698_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4700_ = v___x_4642_;
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4642_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4706_, lean_object* v_b_4707_, lean_object* v_a_4708_, lean_object* v___x_4709_, lean_object* v_only_4710_, lean_object* v_incremental_4711_, lean_object* v_x_4712_, lean_object* v_mod_x3f_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
uint8_t v___x_24111__boxed_4721_; uint8_t v_only_boxed_4722_; uint8_t v_incremental_boxed_4723_; lean_object* v_res_4724_; 
v___x_24111__boxed_4721_ = lean_unbox(v___x_4709_);
v_only_boxed_4722_ = lean_unbox(v_only_4710_);
v_incremental_boxed_4723_ = lean_unbox(v_incremental_4711_);
v_res_4724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4706_, v_b_4707_, v_a_4708_, v___x_24111__boxed_4721_, v_only_boxed_4722_, v_incremental_boxed_4723_, v_x_4712_, v_mod_x3f_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___x_4706_);
return v_res_4724_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4733_ = l_Lean_stringToMessageData(v___x_4732_);
return v___x_4733_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15(void){
_start:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14));
v___x_4763_ = l_Lean_stringToMessageData(v___x_4762_);
return v___x_4763_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4766_ = l_Lean_stringToMessageData(v___x_4765_);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4767_, uint8_t v_only_4768_, uint8_t v_incremental_4769_, lean_object* v_as_4770_, size_t v_sz_4771_, size_t v_i_4772_, lean_object* v_b_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v_snd_4782_; lean_object* v___y_4787_; uint8_t v___y_4788_; lean_object* v_a_4793_; lean_object* v___y_4797_; uint8_t v___x_4801_; 
v___x_4801_ = lean_usize_dec_lt(v_i_4772_, v_sz_4771_);
if (v___x_4801_ == 0)
{
lean_object* v___x_4802_; 
v___x_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4802_, 0, v_b_4773_);
return v___x_4802_;
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4804_; uint8_t v___x_4805_; 
v_a_4803_ = lean_array_uget_borrowed(v_as_4770_, v_i_4772_);
v___x_4804_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_4803_);
v___x_4805_ = l_Lean_Syntax_isOfKind(v_a_4803_, v___x_4804_);
if (v___x_4805_ == 0)
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4806_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4803_);
v___x_4807_ = l_Lean_MessageData_ofSyntax(v_a_4803_);
v___x_4808_ = l_Lean_indentD(v___x_4807_);
v___x_4809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4809_, 0, v___x_4806_);
lean_ctor_set(v___x_4809_, 1, v___x_4808_);
v___x_4810_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4809_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_dec_ref_known(v___x_4810_, 1);
v_snd_4782_ = v_b_4773_;
goto v___jp_4781_;
}
else
{
lean_object* v_a_4811_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
lean_inc(v_a_4811_);
lean_dec_ref_known(v___x_4810_, 1);
v_a_4793_ = v_a_4811_;
goto v___jp_4792_;
}
}
else
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; uint8_t v___x_4815_; 
v___x_4812_ = lean_unsigned_to_nat(0u);
v___x_4813_ = l_Lean_Syntax_getArg(v_a_4803_, v___x_4812_);
v___x_4814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_4813_);
v___x_4815_ = l_Lean_Syntax_isOfKind(v___x_4813_, v___x_4814_);
if (v___x_4815_ == 0)
{
lean_object* v___x_4816_; uint8_t v___x_4817_; 
v___x_4816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_4813_);
v___x_4817_ = l_Lean_Syntax_isOfKind(v___x_4813_, v___x_4816_);
if (v___x_4817_ == 0)
{
lean_object* v___x_4818_; uint8_t v___x_4819_; 
v___x_4818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_4813_);
v___x_4819_ = l_Lean_Syntax_isOfKind(v___x_4813_, v___x_4818_);
if (v___x_4819_ == 0)
{
lean_object* v___x_4820_; uint8_t v___x_4821_; 
v___x_4820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_4813_);
v___x_4821_ = l_Lean_Syntax_isOfKind(v___x_4813_, v___x_4820_);
if (v___x_4821_ == 0)
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
lean_dec(v___x_4813_);
v___x_4822_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4803_);
v___x_4823_ = l_Lean_MessageData_ofSyntax(v_a_4803_);
v___x_4824_ = l_Lean_indentD(v___x_4823_);
v___x_4825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4822_);
lean_ctor_set(v___x_4825_, 1, v___x_4824_);
v___x_4826_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4825_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_dec_ref_known(v___x_4826_, 1);
v_snd_4782_ = v_b_4773_;
goto v___jp_4781_;
}
else
{
lean_object* v_a_4827_; 
v_a_4827_ = lean_ctor_get(v___x_4826_, 0);
lean_inc(v_a_4827_);
lean_dec_ref_known(v___x_4826_, 1);
v_a_4793_ = v_a_4827_;
goto v___jp_4792_;
}
}
else
{
lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; uint8_t v___x_4831_; 
v___x_4828_ = lean_unsigned_to_nat(1u);
v___x_4829_ = l_Lean_Syntax_getArg(v___x_4813_, v___x_4828_);
lean_dec(v___x_4813_);
v___x_4830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13));
lean_inc(v___x_4829_);
v___x_4831_ = l_Lean_Syntax_isOfKind(v___x_4829_, v___x_4830_);
if (v___x_4831_ == 0)
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
lean_dec(v___x_4829_);
v___x_4832_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4803_);
v___x_4833_ = l_Lean_MessageData_ofSyntax(v_a_4803_);
v___x_4834_ = l_Lean_indentD(v___x_4833_);
v___x_4835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4832_);
lean_ctor_set(v___x_4835_, 1, v___x_4834_);
v___x_4836_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4835_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_dec_ref_known(v___x_4836_, 1);
v_snd_4782_ = v_b_4773_;
goto v___jp_4781_;
}
else
{
lean_object* v_a_4837_; 
v_a_4837_ = lean_ctor_get(v___x_4836_, 0);
lean_inc(v_a_4837_);
lean_dec_ref_known(v___x_4836_, 1);
v_a_4793_ = v_a_4837_;
goto v___jp_4792_;
}
}
else
{
if (v_only_4768_ == 0)
{
lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4838_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15);
v___x_4839_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_4829_, v___x_4838_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4839_) == 0)
{
lean_object* v_a_4840_; lean_object* v___x_4841_; 
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
lean_inc(v_a_4840_);
lean_dec_ref_known(v___x_4839_, 1);
lean_inc_ref(v_b_4773_);
v___x_4841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4773_, v___x_4829_, v_a_4840_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
lean_dec(v___x_4829_);
v___y_4797_ = v___x_4841_;
goto v___jp_4796_;
}
else
{
lean_object* v_a_4842_; 
lean_dec(v___x_4829_);
v_a_4842_ = lean_ctor_get(v___x_4839_, 0);
lean_inc(v_a_4842_);
lean_dec_ref_known(v___x_4839_, 1);
v_a_4793_ = v_a_4842_;
goto v___jp_4792_;
}
}
else
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = lean_box(0);
lean_inc_ref(v_b_4773_);
v___x_4844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4773_, v___x_4829_, v___x_4843_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
lean_dec(v___x_4829_);
v___y_4797_ = v___x_4844_;
goto v___jp_4796_;
}
}
}
}
else
{
lean_object* v___x_4845_; lean_object* v___x_4846_; uint8_t v___x_4847_; 
v___x_4845_ = lean_unsigned_to_nat(1u);
v___x_4846_ = l_Lean_Syntax_getArg(v___x_4813_, v___x_4845_);
v___x_4847_ = l_Lean_Syntax_isNone(v___x_4846_);
if (v___x_4847_ == 0)
{
uint8_t v___x_4848_; 
lean_inc(v___x_4846_);
v___x_4848_ = l_Lean_Syntax_matchesNull(v___x_4846_, v___x_4845_);
if (v___x_4848_ == 0)
{
lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
lean_dec(v___x_4846_);
lean_dec(v___x_4813_);
v___x_4849_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4803_);
v___x_4850_ = l_Lean_MessageData_ofSyntax(v_a_4803_);
v___x_4851_ = l_Lean_indentD(v___x_4850_);
v___x_4852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4849_);
lean_ctor_set(v___x_4852_, 1, v___x_4851_);
v___x_4853_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4852_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_dec_ref_known(v___x_4853_, 1);
v_snd_4782_ = v_b_4773_;
goto v___jp_4781_;
}
else
{
lean_object* v_a_4854_; 
v_a_4854_ = lean_ctor_get(v___x_4853_, 0);
lean_inc(v_a_4854_);
lean_dec_ref_known(v___x_4853_, 1);
v_a_4793_ = v_a_4854_;
goto v___jp_4792_;
}
}
else
{
lean_object* v___x_4855_; lean_object* v___x_4856_; uint8_t v___x_4857_; 
v___x_4855_ = l_Lean_Syntax_getArg(v___x_4846_, v___x_4812_);
lean_dec(v___x_4846_);
v___x_4856_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4855_);
v___x_4857_ = l_Lean_Syntax_isOfKind(v___x_4855_, v___x_4856_);
if (v___x_4857_ == 0)
{
lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
lean_dec(v___x_4855_);
lean_dec(v___x_4813_);
v___x_4858_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4803_);
v___x_4859_ = l_Lean_MessageData_ofSyntax(v_a_4803_);
v___x_4860_ = l_Lean_indentD(v___x_4859_);
v___x_4861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4861_, 0, v___x_4858_);
lean_ctor_set(v___x_4861_, 1, v___x_4860_);
v___x_4862_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4861_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_dec_ref_known(v___x_4862_, 1);
v_snd_4782_ = v_b_4773_;
goto v___jp_4781_;
}
else
{
lean_object* v_a_4863_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
lean_inc(v_a_4863_);
lean_dec_ref_known(v___x_4862_, 1);
v_a_4793_ = v_a_4863_;
goto v___jp_4792_;
}
}
else
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4864_ = lean_box(0);
v___x_4865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4855_);
lean_inc(v_a_4803_);
lean_inc_ref(v_b_4773_);
v___x_4866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4813_, v_b_4773_, v_a_4803_, v___x_4801_, v_only_4768_, v_incremental_4769_, v___x_4864_, v___x_4865_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
lean_dec(v___x_4813_);
v___y_4797_ = v___x_4866_;
goto v___jp_4796_;
}
}
}
else
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
lean_dec(v___x_4846_);
v___x_4867_ = lean_box(0);
v___x_4868_ = lean_box(0);
lean_inc(v_a_4803_);
lean_inc_ref(v_b_4773_);
v___x_4869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4813_, v_b_4773_, v_a_4803_, v___x_4801_, v_only_4768_, v_incremental_4769_, v___x_4867_, v___x_4868_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
lean_dec(v___x_4813_);
v___y_4797_ = v___x_4869_;
goto v___jp_4796_;
}
}
}
else
{
lean_object* v___x_4870_; uint8_t v___x_4871_; 
v___x_4870_ = l_Lean_Syntax_getArg(v___x_4813_, v___x_4812_);
v___x_4871_ = l_Lean_Syntax_isNone(v___x_4870_);
if (v___x_4871_ == 0)
{
lean_object* v___x_4872_; uint8_t v___x_4873_; 
v___x_4872_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4870_);
v___x_4873_ = l_Lean_Syntax_matchesNull(v___x_4870_, v___x_4872_);
if (v___x_4873_ == 0)
{
lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
lean_dec(v___x_4870_);
lean_dec(v___x_4813_);
v___x_4874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4803_);
v___x_4875_ = l_Lean_MessageData_ofSyntax(v_a_4803_);
v___x_4876_ = l_Lean_indentD(v___x_4875_);
v___x_4877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4874_);
lean_ctor_set(v___x_4877_, 1, v___x_4876_);
v___x_4878_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4877_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_dec_ref_known(v___x_4878_, 1);
v_snd_4782_ = v_b_4773_;
goto v___jp_4781_;
}
else
{
lean_object* v_a_4879_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
lean_inc(v_a_4879_);
lean_dec_ref_known(v___x_4878_, 1);
v_a_4793_ = v_a_4879_;
goto v___jp_4792_;
}
}
else
{
lean_object* v___x_4880_; lean_object* v___x_4881_; uint8_t v___x_4882_; 
v___x_4880_ = l_Lean_Syntax_getArg(v___x_4870_, v___x_4812_);
lean_dec(v___x_4870_);
v___x_4881_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4880_);
v___x_4882_ = l_Lean_Syntax_isOfKind(v___x_4880_, v___x_4881_);
if (v___x_4882_ == 0)
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
lean_dec(v___x_4880_);
lean_dec(v___x_4813_);
v___x_4883_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4803_);
v___x_4884_ = l_Lean_MessageData_ofSyntax(v_a_4803_);
v___x_4885_ = l_Lean_indentD(v___x_4884_);
v___x_4886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4883_);
lean_ctor_set(v___x_4886_, 1, v___x_4885_);
v___x_4887_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4886_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_dec_ref_known(v___x_4887_, 1);
v_snd_4782_ = v_b_4773_;
goto v___jp_4781_;
}
else
{
lean_object* v_a_4888_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref_known(v___x_4887_, 1);
v_a_4793_ = v_a_4888_;
goto v___jp_4792_;
}
}
else
{
lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4889_ = lean_box(0);
v___x_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4880_);
lean_inc(v_a_4803_);
lean_inc_ref(v_b_4773_);
v___x_4891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4813_, v_b_4773_, v_a_4803_, v___x_4815_, v_only_4768_, v_incremental_4769_, v___x_4889_, v___x_4890_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
lean_dec(v___x_4813_);
v___y_4797_ = v___x_4891_;
goto v___jp_4796_;
}
}
}
else
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; 
lean_dec(v___x_4870_);
v___x_4892_ = lean_box(0);
v___x_4893_ = lean_box(0);
lean_inc(v_a_4803_);
lean_inc_ref(v_b_4773_);
v___x_4894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4813_, v_b_4773_, v_a_4803_, v___x_4815_, v_only_4768_, v_incremental_4769_, v___x_4892_, v___x_4893_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
lean_dec(v___x_4813_);
v___y_4797_ = v___x_4894_;
goto v___jp_4796_;
}
}
}
else
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; uint8_t v___x_4898_; 
v___x_4895_ = lean_unsigned_to_nat(1u);
v___x_4896_ = l_Lean_Syntax_getArg(v___x_4813_, v___x_4895_);
lean_dec(v___x_4813_);
v___x_4897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4896_);
v___x_4898_ = l_Lean_Syntax_isOfKind(v___x_4896_, v___x_4897_);
if (v___x_4898_ == 0)
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
lean_dec(v___x_4896_);
v___x_4899_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4803_);
v___x_4900_ = l_Lean_MessageData_ofSyntax(v_a_4803_);
v___x_4901_ = l_Lean_indentD(v___x_4900_);
v___x_4902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4899_);
lean_ctor_set(v___x_4902_, 1, v___x_4901_);
v___x_4903_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4902_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4903_) == 0)
{
lean_dec_ref_known(v___x_4903_, 1);
v_snd_4782_ = v_b_4773_;
goto v___jp_4781_;
}
else
{
lean_object* v_a_4904_; 
v_a_4904_ = lean_ctor_get(v___x_4903_, 0);
lean_inc(v_a_4904_);
lean_dec_ref_known(v___x_4903_, 1);
v_a_4793_ = v_a_4904_;
goto v___jp_4792_;
}
}
else
{
if (v_incremental_4769_ == 0)
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4905_ = lean_box(0);
lean_inc_ref(v_b_4773_);
v___x_4906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4896_, v_b_4773_, v___x_4905_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
v___y_4797_ = v___x_4906_;
goto v___jp_4796_;
}
else
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4907_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_4908_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_4803_, v___x_4907_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v___x_4910_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4909_);
lean_dec_ref_known(v___x_4908_, 1);
lean_inc_ref(v_b_4773_);
v___x_4910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4896_, v_b_4773_, v_a_4909_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
v___y_4797_ = v___x_4910_;
goto v___jp_4796_;
}
else
{
lean_object* v_a_4911_; 
lean_dec(v___x_4896_);
v_a_4911_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4908_, 1);
v_a_4793_ = v_a_4911_;
goto v___jp_4792_;
}
}
}
}
}
}
v___jp_4781_:
{
size_t v___x_4783_; size_t v___x_4784_; 
v___x_4783_ = ((size_t)1ULL);
v___x_4784_ = lean_usize_add(v_i_4772_, v___x_4783_);
v_i_4772_ = v___x_4784_;
v_b_4773_ = v_snd_4782_;
goto _start;
}
v___jp_4786_:
{
if (v___y_4788_ == 0)
{
uint8_t v___x_4789_; 
v___x_4789_ = lean_bool_not(v_lax_4767_);
if (v___x_4789_ == 0)
{
lean_dec_ref(v___y_4787_);
v_snd_4782_ = v_b_4773_;
goto v___jp_4781_;
}
else
{
lean_object* v___x_4790_; 
lean_dec_ref(v_b_4773_);
v___x_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4790_, 0, v___y_4787_);
return v___x_4790_;
}
}
else
{
lean_object* v___x_4791_; 
lean_dec_ref(v_b_4773_);
v___x_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4791_, 0, v___y_4787_);
return v___x_4791_;
}
}
v___jp_4792_:
{
uint8_t v___x_4794_; 
v___x_4794_ = l_Lean_Exception_isInterrupt(v_a_4793_);
if (v___x_4794_ == 0)
{
uint8_t v___x_4795_; 
lean_inc_ref(v_a_4793_);
v___x_4795_ = l_Lean_Exception_isRuntime(v_a_4793_);
v___y_4787_ = v_a_4793_;
v___y_4788_ = v___x_4795_;
goto v___jp_4786_;
}
else
{
v___y_4787_ = v_a_4793_;
v___y_4788_ = v___x_4794_;
goto v___jp_4786_;
}
}
v___jp_4796_:
{
if (lean_obj_tag(v___y_4797_) == 0)
{
lean_object* v_a_4798_; lean_object* v_snd_4799_; 
lean_dec_ref(v_b_4773_);
v_a_4798_ = lean_ctor_get(v___y_4797_, 0);
lean_inc(v_a_4798_);
lean_dec_ref_known(v___y_4797_, 1);
v_snd_4799_ = lean_ctor_get(v_a_4798_, 1);
lean_inc(v_snd_4799_);
lean_dec(v_a_4798_);
v_snd_4782_ = v_snd_4799_;
goto v___jp_4781_;
}
else
{
lean_object* v_a_4800_; 
v_a_4800_ = lean_ctor_get(v___y_4797_, 0);
lean_inc(v_a_4800_);
lean_dec_ref_known(v___y_4797_, 1);
v_a_4793_ = v_a_4800_;
goto v___jp_4792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_4912_, lean_object* v_only_4913_, lean_object* v_incremental_4914_, lean_object* v_as_4915_, lean_object* v_sz_4916_, lean_object* v_i_4917_, lean_object* v_b_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
uint8_t v_lax_boxed_4926_; uint8_t v_only_boxed_4927_; uint8_t v_incremental_boxed_4928_; size_t v_sz_boxed_4929_; size_t v_i_boxed_4930_; lean_object* v_res_4931_; 
v_lax_boxed_4926_ = lean_unbox(v_lax_4912_);
v_only_boxed_4927_ = lean_unbox(v_only_4913_);
v_incremental_boxed_4928_ = lean_unbox(v_incremental_4914_);
v_sz_boxed_4929_ = lean_unbox_usize(v_sz_4916_);
lean_dec(v_sz_4916_);
v_i_boxed_4930_ = lean_unbox_usize(v_i_4917_);
lean_dec(v_i_4917_);
v_res_4931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_4926_, v_only_boxed_4927_, v_incremental_boxed_4928_, v_as_4915_, v_sz_boxed_4929_, v_i_boxed_4930_, v_b_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec(v___y_4922_);
lean_dec_ref(v___y_4921_);
lean_dec(v___y_4920_);
lean_dec_ref(v___y_4919_);
lean_dec_ref(v_as_4915_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_4932_, lean_object* v_ps_4933_, uint8_t v_only_4934_, uint8_t v_lax_4935_, uint8_t v_incremental_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_){
_start:
{
size_t v_sz_4944_; size_t v___x_4945_; lean_object* v___x_4946_; 
v_sz_4944_ = lean_array_size(v_ps_4933_);
v___x_4945_ = ((size_t)0ULL);
v___x_4946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_4935_, v_only_4934_, v_incremental_4936_, v_ps_4933_, v_sz_4944_, v___x_4945_, v_params_4932_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_4947_, lean_object* v_ps_4948_, lean_object* v_only_4949_, lean_object* v_lax_4950_, lean_object* v_incremental_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_){
_start:
{
uint8_t v_only_boxed_4959_; uint8_t v_lax_boxed_4960_; uint8_t v_incremental_boxed_4961_; lean_object* v_res_4962_; 
v_only_boxed_4959_ = lean_unbox(v_only_4949_);
v_lax_boxed_4960_ = lean_unbox(v_lax_4950_);
v_incremental_boxed_4961_ = lean_unbox(v_incremental_4951_);
v_res_4962_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_4947_, v_ps_4948_, v_only_boxed_4959_, v_lax_boxed_4960_, v_incremental_boxed_4961_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_);
lean_dec(v_a_4957_);
lean_dec_ref(v_a_4956_);
lean_dec(v_a_4955_);
lean_dec_ref(v_a_4954_);
lean_dec(v_a_4953_);
lean_dec_ref(v_a_4952_);
lean_dec_ref(v_ps_4948_);
return v_res_4962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_){
_start:
{
lean_object* v_origin_4974_; 
v_origin_4974_ = lean_ctor_get(v_thm_4963_, 5);
if (lean_obj_tag(v_origin_4974_) == 0)
{
lean_object* v_declName_4975_; lean_object* v___x_4976_; 
lean_inc_ref(v_origin_4974_);
lean_dec_ref(v_thm_4963_);
v_declName_4975_ = lean_ctor_get(v_origin_4974_, 0);
lean_inc(v_declName_4975_);
lean_dec_ref_known(v_origin_4974_, 1);
v___x_4976_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_4975_, v_a_4971_, v_a_4972_);
return v___x_4976_;
}
else
{
lean_object* v_proof_4977_; lean_object* v___x_4978_; 
v_proof_4977_ = lean_ctor_get(v_thm_4963_, 1);
lean_inc_ref(v_proof_4977_);
lean_dec_ref(v_thm_4963_);
v___x_4978_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_4977_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
return v___x_4978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_);
lean_dec(v_a_4988_);
lean_dec_ref(v_a_4987_);
lean_dec(v_a_4986_);
lean_dec_ref(v_a_4985_);
lean_dec(v_a_4984_);
lean_dec_ref(v_a_4983_);
lean_dec(v_a_4982_);
lean_dec_ref(v_a_4981_);
lean_dec(v_a_4980_);
return v_res_4990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_4991_, size_t v_sz_4992_, size_t v_i_4993_, lean_object* v_b_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_){
_start:
{
uint8_t v___x_5005_; 
v___x_5005_ = lean_usize_dec_lt(v_i_4993_, v_sz_4992_);
if (v___x_5005_ == 0)
{
lean_object* v___x_5006_; 
v___x_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5006_, 0, v_b_4994_);
return v___x_5006_;
}
else
{
lean_object* v_snd_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5033_; 
v_snd_5007_ = lean_ctor_get(v_b_4994_, 1);
v_isSharedCheck_5033_ = !lean_is_exclusive(v_b_4994_);
if (v_isSharedCheck_5033_ == 0)
{
lean_object* v_unused_5034_; 
v_unused_5034_ = lean_ctor_get(v_b_4994_, 0);
lean_dec(v_unused_5034_);
v___x_5009_ = v_b_4994_;
v_isShared_5010_ = v_isSharedCheck_5033_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_snd_5007_);
lean_dec(v_b_4994_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5033_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v_a_5011_; lean_object* v___x_5012_; 
v_a_5011_ = lean_array_uget_borrowed(v_as_4991_, v_i_4993_);
lean_inc(v_a_5011_);
v___x_5012_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5011_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; lean_object* v___x_5014_; lean_object* v_a_5016_; uint8_t v___x_5023_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
lean_inc(v_a_5013_);
lean_dec_ref_known(v___x_5012_, 1);
v___x_5014_ = lean_box(0);
v___x_5023_ = lean_unbox(v_a_5013_);
lean_dec(v_a_5013_);
if (v___x_5023_ == 0)
{
v_a_5016_ = v_snd_5007_;
goto v___jp_5015_;
}
else
{
lean_object* v___x_5024_; 
lean_inc(v_a_5011_);
v___x_5024_ = l_Lean_PersistentArray_push___redArg(v_snd_5007_, v_a_5011_);
v_a_5016_ = v___x_5024_;
goto v___jp_5015_;
}
v___jp_5015_:
{
lean_object* v___x_5018_; 
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 1, v_a_5016_);
lean_ctor_set(v___x_5009_, 0, v___x_5014_);
v___x_5018_ = v___x_5009_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5014_);
lean_ctor_set(v_reuseFailAlloc_5022_, 1, v_a_5016_);
v___x_5018_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
size_t v___x_5019_; size_t v___x_5020_; 
v___x_5019_ = ((size_t)1ULL);
v___x_5020_ = lean_usize_add(v_i_4993_, v___x_5019_);
v_i_4993_ = v___x_5020_;
v_b_4994_ = v___x_5018_;
goto _start;
}
}
}
else
{
lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5032_; 
lean_del_object(v___x_5009_);
lean_dec(v_snd_5007_);
v_a_5025_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5027_ = v___x_5012_;
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_5012_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5030_; 
if (v_isShared_5028_ == 0)
{
v___x_5030_ = v___x_5027_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_a_5025_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5035_, lean_object* v_sz_5036_, lean_object* v_i_5037_, lean_object* v_b_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_){
_start:
{
size_t v_sz_boxed_5049_; size_t v_i_boxed_5050_; lean_object* v_res_5051_; 
v_sz_boxed_5049_ = lean_unbox_usize(v_sz_5036_);
lean_dec(v_sz_5036_);
v_i_boxed_5050_ = lean_unbox_usize(v_i_5037_);
lean_dec(v_i_5037_);
v_res_5051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5035_, v_sz_boxed_5049_, v_i_boxed_5050_, v_b_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_);
lean_dec(v___y_5047_);
lean_dec_ref(v___y_5046_);
lean_dec(v___y_5045_);
lean_dec_ref(v___y_5044_);
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5042_);
lean_dec(v___y_5041_);
lean_dec_ref(v___y_5040_);
lean_dec(v___y_5039_);
lean_dec_ref(v_as_5035_);
return v_res_5051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5052_, size_t v_sz_5053_, size_t v_i_5054_, lean_object* v_b_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_){
_start:
{
uint8_t v___x_5066_; 
v___x_5066_ = lean_usize_dec_lt(v_i_5054_, v_sz_5053_);
if (v___x_5066_ == 0)
{
lean_object* v___x_5067_; 
v___x_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5067_, 0, v_b_5055_);
return v___x_5067_;
}
else
{
lean_object* v_snd_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5094_; 
v_snd_5068_ = lean_ctor_get(v_b_5055_, 1);
v_isSharedCheck_5094_ = !lean_is_exclusive(v_b_5055_);
if (v_isSharedCheck_5094_ == 0)
{
lean_object* v_unused_5095_; 
v_unused_5095_ = lean_ctor_get(v_b_5055_, 0);
lean_dec(v_unused_5095_);
v___x_5070_ = v_b_5055_;
v_isShared_5071_ = v_isSharedCheck_5094_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_snd_5068_);
lean_dec(v_b_5055_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5094_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v_a_5072_; lean_object* v___x_5073_; 
v_a_5072_ = lean_array_uget_borrowed(v_as_5052_, v_i_5054_);
lean_inc(v_a_5072_);
v___x_5073_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5072_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_object* v_a_5074_; lean_object* v___x_5075_; lean_object* v_a_5077_; uint8_t v___x_5084_; 
v_a_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_a_5074_);
lean_dec_ref_known(v___x_5073_, 1);
v___x_5075_ = lean_box(0);
v___x_5084_ = lean_unbox(v_a_5074_);
lean_dec(v_a_5074_);
if (v___x_5084_ == 0)
{
v_a_5077_ = v_snd_5068_;
goto v___jp_5076_;
}
else
{
lean_object* v___x_5085_; 
lean_inc(v_a_5072_);
v___x_5085_ = l_Lean_PersistentArray_push___redArg(v_snd_5068_, v_a_5072_);
v_a_5077_ = v___x_5085_;
goto v___jp_5076_;
}
v___jp_5076_:
{
lean_object* v___x_5079_; 
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 1, v_a_5077_);
lean_ctor_set(v___x_5070_, 0, v___x_5075_);
v___x_5079_ = v___x_5070_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v___x_5075_);
lean_ctor_set(v_reuseFailAlloc_5083_, 1, v_a_5077_);
v___x_5079_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
size_t v___x_5080_; size_t v___x_5081_; lean_object* v___x_5082_; 
v___x_5080_ = ((size_t)1ULL);
v___x_5081_ = lean_usize_add(v_i_5054_, v___x_5080_);
v___x_5082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5052_, v_sz_5053_, v___x_5081_, v___x_5079_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
return v___x_5082_;
}
}
}
else
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
lean_del_object(v___x_5070_);
lean_dec(v_snd_5068_);
v_a_5086_ = lean_ctor_get(v___x_5073_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5073_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5073_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5073_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5096_, lean_object* v_sz_5097_, lean_object* v_i_5098_, lean_object* v_b_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_){
_start:
{
size_t v_sz_boxed_5110_; size_t v_i_boxed_5111_; lean_object* v_res_5112_; 
v_sz_boxed_5110_ = lean_unbox_usize(v_sz_5097_);
lean_dec(v_sz_5097_);
v_i_boxed_5111_ = lean_unbox_usize(v_i_5098_);
lean_dec(v_i_5098_);
v_res_5112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5096_, v_sz_boxed_5110_, v_i_boxed_5111_, v_b_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_);
lean_dec(v___y_5108_);
lean_dec_ref(v___y_5107_);
lean_dec(v___y_5106_);
lean_dec_ref(v___y_5105_);
lean_dec(v___y_5104_);
lean_dec_ref(v___y_5103_);
lean_dec(v___y_5102_);
lean_dec_ref(v___y_5101_);
lean_dec(v___y_5100_);
lean_dec_ref(v_as_5096_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5113_, size_t v_sz_5114_, size_t v_i_5115_, lean_object* v_b_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
uint8_t v___x_5127_; 
v___x_5127_ = lean_usize_dec_lt(v_i_5115_, v_sz_5114_);
if (v___x_5127_ == 0)
{
lean_object* v___x_5128_; 
v___x_5128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5128_, 0, v_b_5116_);
return v___x_5128_;
}
else
{
lean_object* v_snd_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5155_; 
v_snd_5129_ = lean_ctor_get(v_b_5116_, 1);
v_isSharedCheck_5155_ = !lean_is_exclusive(v_b_5116_);
if (v_isSharedCheck_5155_ == 0)
{
lean_object* v_unused_5156_; 
v_unused_5156_ = lean_ctor_get(v_b_5116_, 0);
lean_dec(v_unused_5156_);
v___x_5131_ = v_b_5116_;
v_isShared_5132_ = v_isSharedCheck_5155_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_snd_5129_);
lean_dec(v_b_5116_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5155_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v_a_5133_; lean_object* v___x_5134_; 
v_a_5133_ = lean_array_uget_borrowed(v_as_5113_, v_i_5115_);
lean_inc(v_a_5133_);
v___x_5134_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5133_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; lean_object* v___x_5136_; lean_object* v_a_5138_; uint8_t v___x_5145_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5134_, 1);
v___x_5136_ = lean_box(0);
v___x_5145_ = lean_unbox(v_a_5135_);
lean_dec(v_a_5135_);
if (v___x_5145_ == 0)
{
v_a_5138_ = v_snd_5129_;
goto v___jp_5137_;
}
else
{
lean_object* v___x_5146_; 
lean_inc(v_a_5133_);
v___x_5146_ = l_Lean_PersistentArray_push___redArg(v_snd_5129_, v_a_5133_);
v_a_5138_ = v___x_5146_;
goto v___jp_5137_;
}
v___jp_5137_:
{
lean_object* v___x_5140_; 
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 1, v_a_5138_);
lean_ctor_set(v___x_5131_, 0, v___x_5136_);
v___x_5140_ = v___x_5131_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v___x_5136_);
lean_ctor_set(v_reuseFailAlloc_5144_, 1, v_a_5138_);
v___x_5140_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
size_t v___x_5141_; size_t v___x_5142_; 
v___x_5141_ = ((size_t)1ULL);
v___x_5142_ = lean_usize_add(v_i_5115_, v___x_5141_);
v_i_5115_ = v___x_5142_;
v_b_5116_ = v___x_5140_;
goto _start;
}
}
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
lean_del_object(v___x_5131_);
lean_dec(v_snd_5129_);
v_a_5147_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_5134_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5134_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5157_, lean_object* v_sz_5158_, lean_object* v_i_5159_, lean_object* v_b_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_){
_start:
{
size_t v_sz_boxed_5171_; size_t v_i_boxed_5172_; lean_object* v_res_5173_; 
v_sz_boxed_5171_ = lean_unbox_usize(v_sz_5158_);
lean_dec(v_sz_5158_);
v_i_boxed_5172_ = lean_unbox_usize(v_i_5159_);
lean_dec(v_i_5159_);
v_res_5173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5157_, v_sz_boxed_5171_, v_i_boxed_5172_, v_b_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
lean_dec(v___y_5161_);
lean_dec_ref(v_as_5157_);
return v_res_5173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5174_, size_t v_sz_5175_, size_t v_i_5176_, lean_object* v_b_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_){
_start:
{
uint8_t v___x_5188_; 
v___x_5188_ = lean_usize_dec_lt(v_i_5176_, v_sz_5175_);
if (v___x_5188_ == 0)
{
lean_object* v___x_5189_; 
v___x_5189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5189_, 0, v_b_5177_);
return v___x_5189_;
}
else
{
lean_object* v_snd_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5216_; 
v_snd_5190_ = lean_ctor_get(v_b_5177_, 1);
v_isSharedCheck_5216_ = !lean_is_exclusive(v_b_5177_);
if (v_isSharedCheck_5216_ == 0)
{
lean_object* v_unused_5217_; 
v_unused_5217_ = lean_ctor_get(v_b_5177_, 0);
lean_dec(v_unused_5217_);
v___x_5192_ = v_b_5177_;
v_isShared_5193_ = v_isSharedCheck_5216_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_snd_5190_);
lean_dec(v_b_5177_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5216_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v_a_5194_; lean_object* v___x_5195_; 
v_a_5194_ = lean_array_uget_borrowed(v_as_5174_, v_i_5176_);
lean_inc(v_a_5194_);
v___x_5195_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5194_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_);
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_object* v_a_5196_; lean_object* v___x_5197_; lean_object* v_a_5199_; uint8_t v___x_5206_; 
v_a_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc(v_a_5196_);
lean_dec_ref_known(v___x_5195_, 1);
v___x_5197_ = lean_box(0);
v___x_5206_ = lean_unbox(v_a_5196_);
lean_dec(v_a_5196_);
if (v___x_5206_ == 0)
{
v_a_5199_ = v_snd_5190_;
goto v___jp_5198_;
}
else
{
lean_object* v___x_5207_; 
lean_inc(v_a_5194_);
v___x_5207_ = l_Lean_PersistentArray_push___redArg(v_snd_5190_, v_a_5194_);
v_a_5199_ = v___x_5207_;
goto v___jp_5198_;
}
v___jp_5198_:
{
lean_object* v___x_5201_; 
if (v_isShared_5193_ == 0)
{
lean_ctor_set(v___x_5192_, 1, v_a_5199_);
lean_ctor_set(v___x_5192_, 0, v___x_5197_);
v___x_5201_ = v___x_5192_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v___x_5197_);
lean_ctor_set(v_reuseFailAlloc_5205_, 1, v_a_5199_);
v___x_5201_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
size_t v___x_5202_; size_t v___x_5203_; lean_object* v___x_5204_; 
v___x_5202_ = ((size_t)1ULL);
v___x_5203_ = lean_usize_add(v_i_5176_, v___x_5202_);
v___x_5204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5174_, v_sz_5175_, v___x_5203_, v___x_5201_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_);
return v___x_5204_;
}
}
}
else
{
lean_object* v_a_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5215_; 
lean_del_object(v___x_5192_);
lean_dec(v_snd_5190_);
v_a_5208_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5210_ = v___x_5195_;
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v___x_5195_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5213_; 
if (v_isShared_5211_ == 0)
{
v___x_5213_ = v___x_5210_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
v___x_5213_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
return v___x_5213_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5218_, lean_object* v_sz_5219_, lean_object* v_i_5220_, lean_object* v_b_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
size_t v_sz_boxed_5232_; size_t v_i_boxed_5233_; lean_object* v_res_5234_; 
v_sz_boxed_5232_ = lean_unbox_usize(v_sz_5219_);
lean_dec(v_sz_5219_);
v_i_boxed_5233_ = lean_unbox_usize(v_i_5220_);
lean_dec(v_i_5220_);
v_res_5234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5218_, v_sz_boxed_5232_, v_i_boxed_5233_, v_b_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_);
lean_dec(v___y_5230_);
lean_dec_ref(v___y_5229_);
lean_dec(v___y_5228_);
lean_dec_ref(v___y_5227_);
lean_dec(v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
lean_dec(v___y_5222_);
lean_dec_ref(v_as_5218_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5235_, lean_object* v_n_5236_, lean_object* v_b_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_){
_start:
{
if (lean_obj_tag(v_n_5236_) == 0)
{
lean_object* v_cs_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; size_t v_sz_5251_; size_t v___x_5252_; lean_object* v___x_5253_; 
v_cs_5248_ = lean_ctor_get(v_n_5236_, 0);
v___x_5249_ = lean_box(0);
v___x_5250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5250_, 0, v___x_5249_);
lean_ctor_set(v___x_5250_, 1, v_b_5237_);
v_sz_5251_ = lean_array_size(v_cs_5248_);
v___x_5252_ = ((size_t)0ULL);
v___x_5253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5235_, v_cs_5248_, v_sz_5251_, v___x_5252_, v___x_5250_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_);
if (lean_obj_tag(v___x_5253_) == 0)
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5268_; 
v_a_5254_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5256_ = v___x_5253_;
v_isShared_5257_ = v_isSharedCheck_5268_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5253_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5268_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v_fst_5258_; 
v_fst_5258_ = lean_ctor_get(v_a_5254_, 0);
if (lean_obj_tag(v_fst_5258_) == 0)
{
lean_object* v_snd_5259_; lean_object* v___x_5260_; lean_object* v___x_5262_; 
v_snd_5259_ = lean_ctor_get(v_a_5254_, 1);
lean_inc(v_snd_5259_);
lean_dec(v_a_5254_);
v___x_5260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5260_, 0, v_snd_5259_);
if (v_isShared_5257_ == 0)
{
lean_ctor_set(v___x_5256_, 0, v___x_5260_);
v___x_5262_ = v___x_5256_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___x_5260_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
else
{
lean_object* v_val_5264_; lean_object* v___x_5266_; 
lean_inc_ref(v_fst_5258_);
lean_dec(v_a_5254_);
v_val_5264_ = lean_ctor_get(v_fst_5258_, 0);
lean_inc(v_val_5264_);
lean_dec_ref_known(v_fst_5258_, 1);
if (v_isShared_5257_ == 0)
{
lean_ctor_set(v___x_5256_, 0, v_val_5264_);
v___x_5266_ = v___x_5256_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_val_5264_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
return v___x_5266_;
}
}
}
}
else
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5276_; 
v_a_5269_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5271_ = v___x_5253_;
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_5253_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
}
}
else
{
lean_object* v_vs_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; size_t v_sz_5280_; size_t v___x_5281_; lean_object* v___x_5282_; 
v_vs_5277_ = lean_ctor_get(v_n_5236_, 0);
v___x_5278_ = lean_box(0);
v___x_5279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5278_);
lean_ctor_set(v___x_5279_, 1, v_b_5237_);
v_sz_5280_ = lean_array_size(v_vs_5277_);
v___x_5281_ = ((size_t)0ULL);
v___x_5282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5277_, v_sz_5280_, v___x_5281_, v___x_5279_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_);
if (lean_obj_tag(v___x_5282_) == 0)
{
lean_object* v_a_5283_; lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5297_; 
v_a_5283_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5285_ = v___x_5282_;
v_isShared_5286_ = v_isSharedCheck_5297_;
goto v_resetjp_5284_;
}
else
{
lean_inc(v_a_5283_);
lean_dec(v___x_5282_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5297_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
lean_object* v_fst_5287_; 
v_fst_5287_ = lean_ctor_get(v_a_5283_, 0);
if (lean_obj_tag(v_fst_5287_) == 0)
{
lean_object* v_snd_5288_; lean_object* v___x_5289_; lean_object* v___x_5291_; 
v_snd_5288_ = lean_ctor_get(v_a_5283_, 1);
lean_inc(v_snd_5288_);
lean_dec(v_a_5283_);
v___x_5289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5289_, 0, v_snd_5288_);
if (v_isShared_5286_ == 0)
{
lean_ctor_set(v___x_5285_, 0, v___x_5289_);
v___x_5291_ = v___x_5285_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
else
{
lean_object* v_val_5293_; lean_object* v___x_5295_; 
lean_inc_ref(v_fst_5287_);
lean_dec(v_a_5283_);
v_val_5293_ = lean_ctor_get(v_fst_5287_, 0);
lean_inc(v_val_5293_);
lean_dec_ref_known(v_fst_5287_, 1);
if (v_isShared_5286_ == 0)
{
lean_ctor_set(v___x_5285_, 0, v_val_5293_);
v___x_5295_ = v___x_5285_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_val_5293_);
v___x_5295_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
return v___x_5295_;
}
}
}
}
else
{
lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5305_; 
v_a_5298_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5305_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5305_ == 0)
{
v___x_5300_ = v___x_5282_;
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5282_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5303_; 
if (v_isShared_5301_ == 0)
{
v___x_5303_ = v___x_5300_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5306_, lean_object* v_as_5307_, size_t v_sz_5308_, size_t v_i_5309_, lean_object* v_b_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_){
_start:
{
uint8_t v___x_5321_; 
v___x_5321_ = lean_usize_dec_lt(v_i_5309_, v_sz_5308_);
if (v___x_5321_ == 0)
{
lean_object* v___x_5322_; 
v___x_5322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5322_, 0, v_b_5310_);
return v___x_5322_;
}
else
{
lean_object* v_snd_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5357_; 
v_snd_5323_ = lean_ctor_get(v_b_5310_, 1);
v_isSharedCheck_5357_ = !lean_is_exclusive(v_b_5310_);
if (v_isSharedCheck_5357_ == 0)
{
lean_object* v_unused_5358_; 
v_unused_5358_ = lean_ctor_get(v_b_5310_, 0);
lean_dec(v_unused_5358_);
v___x_5325_ = v_b_5310_;
v_isShared_5326_ = v_isSharedCheck_5357_;
goto v_resetjp_5324_;
}
else
{
lean_inc(v_snd_5323_);
lean_dec(v_b_5310_);
v___x_5325_ = lean_box(0);
v_isShared_5326_ = v_isSharedCheck_5357_;
goto v_resetjp_5324_;
}
v_resetjp_5324_:
{
lean_object* v_a_5327_; lean_object* v___x_5328_; 
v_a_5327_ = lean_array_uget_borrowed(v_as_5307_, v_i_5309_);
lean_inc(v_snd_5323_);
v___x_5328_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5306_, v_a_5327_, v_snd_5323_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_);
if (lean_obj_tag(v___x_5328_) == 0)
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5348_; 
v_a_5329_ = lean_ctor_get(v___x_5328_, 0);
v_isSharedCheck_5348_ = !lean_is_exclusive(v___x_5328_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5331_ = v___x_5328_;
v_isShared_5332_ = v_isSharedCheck_5348_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v___x_5328_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5348_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
if (lean_obj_tag(v_a_5329_) == 0)
{
lean_object* v___x_5333_; lean_object* v___x_5335_; 
v___x_5333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5333_, 0, v_a_5329_);
if (v_isShared_5326_ == 0)
{
lean_ctor_set(v___x_5325_, 0, v___x_5333_);
v___x_5335_ = v___x_5325_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v___x_5333_);
lean_ctor_set(v_reuseFailAlloc_5339_, 1, v_snd_5323_);
v___x_5335_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
lean_object* v___x_5337_; 
if (v_isShared_5332_ == 0)
{
lean_ctor_set(v___x_5331_, 0, v___x_5335_);
v___x_5337_ = v___x_5331_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5338_; 
v_reuseFailAlloc_5338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5338_, 0, v___x_5335_);
v___x_5337_ = v_reuseFailAlloc_5338_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
return v___x_5337_;
}
}
}
else
{
lean_object* v_a_5340_; lean_object* v___x_5341_; lean_object* v___x_5343_; 
lean_del_object(v___x_5331_);
lean_dec(v_snd_5323_);
v_a_5340_ = lean_ctor_get(v_a_5329_, 0);
lean_inc(v_a_5340_);
lean_dec_ref_known(v_a_5329_, 1);
v___x_5341_ = lean_box(0);
if (v_isShared_5326_ == 0)
{
lean_ctor_set(v___x_5325_, 1, v_a_5340_);
lean_ctor_set(v___x_5325_, 0, v___x_5341_);
v___x_5343_ = v___x_5325_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v___x_5341_);
lean_ctor_set(v_reuseFailAlloc_5347_, 1, v_a_5340_);
v___x_5343_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
size_t v___x_5344_; size_t v___x_5345_; 
v___x_5344_ = ((size_t)1ULL);
v___x_5345_ = lean_usize_add(v_i_5309_, v___x_5344_);
v_i_5309_ = v___x_5345_;
v_b_5310_ = v___x_5343_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5356_; 
lean_del_object(v___x_5325_);
lean_dec(v_snd_5323_);
v_a_5349_ = lean_ctor_get(v___x_5328_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5328_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5351_ = v___x_5328_;
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5328_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v___x_5354_; 
if (v_isShared_5352_ == 0)
{
v___x_5354_ = v___x_5351_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5359_, lean_object* v_as_5360_, lean_object* v_sz_5361_, lean_object* v_i_5362_, lean_object* v_b_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_){
_start:
{
size_t v_sz_boxed_5374_; size_t v_i_boxed_5375_; lean_object* v_res_5376_; 
v_sz_boxed_5374_ = lean_unbox_usize(v_sz_5361_);
lean_dec(v_sz_5361_);
v_i_boxed_5375_ = lean_unbox_usize(v_i_5362_);
lean_dec(v_i_5362_);
v_res_5376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5359_, v_as_5360_, v_sz_boxed_5374_, v_i_boxed_5375_, v_b_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
lean_dec(v___y_5368_);
lean_dec_ref(v___y_5367_);
lean_dec(v___y_5366_);
lean_dec_ref(v___y_5365_);
lean_dec(v___y_5364_);
lean_dec_ref(v_as_5360_);
lean_dec_ref(v_init_5359_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5377_, lean_object* v_n_5378_, lean_object* v_b_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
lean_object* v_res_5390_; 
v_res_5390_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5377_, v_n_5378_, v_b_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
lean_dec(v___y_5386_);
lean_dec_ref(v___y_5385_);
lean_dec(v___y_5384_);
lean_dec_ref(v___y_5383_);
lean_dec(v___y_5382_);
lean_dec_ref(v___y_5381_);
lean_dec(v___y_5380_);
lean_dec_ref(v_n_5378_);
lean_dec_ref(v_init_5377_);
return v_res_5390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5391_, lean_object* v_init_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_){
_start:
{
lean_object* v_root_5403_; lean_object* v_tail_5404_; lean_object* v___x_5405_; 
v_root_5403_ = lean_ctor_get(v_t_5391_, 0);
v_tail_5404_ = lean_ctor_get(v_t_5391_, 1);
lean_inc_ref(v_init_5392_);
v___x_5405_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5392_, v_root_5403_, v_init_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
lean_dec_ref(v_init_5392_);
if (lean_obj_tag(v___x_5405_) == 0)
{
lean_object* v_a_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5442_; 
v_a_5406_ = lean_ctor_get(v___x_5405_, 0);
v_isSharedCheck_5442_ = !lean_is_exclusive(v___x_5405_);
if (v_isSharedCheck_5442_ == 0)
{
v___x_5408_ = v___x_5405_;
v_isShared_5409_ = v_isSharedCheck_5442_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_a_5406_);
lean_dec(v___x_5405_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5442_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
if (lean_obj_tag(v_a_5406_) == 0)
{
lean_object* v_a_5410_; lean_object* v___x_5412_; 
v_a_5410_ = lean_ctor_get(v_a_5406_, 0);
lean_inc(v_a_5410_);
lean_dec_ref_known(v_a_5406_, 1);
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 0, v_a_5410_);
v___x_5412_ = v___x_5408_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_a_5410_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
else
{
lean_object* v_a_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; size_t v_sz_5417_; size_t v___x_5418_; lean_object* v___x_5419_; 
lean_del_object(v___x_5408_);
v_a_5414_ = lean_ctor_get(v_a_5406_, 0);
lean_inc(v_a_5414_);
lean_dec_ref_known(v_a_5406_, 1);
v___x_5415_ = lean_box(0);
v___x_5416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5416_, 0, v___x_5415_);
lean_ctor_set(v___x_5416_, 1, v_a_5414_);
v_sz_5417_ = lean_array_size(v_tail_5404_);
v___x_5418_ = ((size_t)0ULL);
v___x_5419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5404_, v_sz_5417_, v___x_5418_, v___x_5416_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v_a_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5433_; 
v_a_5420_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5433_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5422_ = v___x_5419_;
v_isShared_5423_ = v_isSharedCheck_5433_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_a_5420_);
lean_dec(v___x_5419_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5433_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v_fst_5424_; 
v_fst_5424_ = lean_ctor_get(v_a_5420_, 0);
if (lean_obj_tag(v_fst_5424_) == 0)
{
lean_object* v_snd_5425_; lean_object* v___x_5427_; 
v_snd_5425_ = lean_ctor_get(v_a_5420_, 1);
lean_inc(v_snd_5425_);
lean_dec(v_a_5420_);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 0, v_snd_5425_);
v___x_5427_ = v___x_5422_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v_snd_5425_);
v___x_5427_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
return v___x_5427_;
}
}
else
{
lean_object* v_val_5429_; lean_object* v___x_5431_; 
lean_inc_ref(v_fst_5424_);
lean_dec(v_a_5420_);
v_val_5429_ = lean_ctor_get(v_fst_5424_, 0);
lean_inc(v_val_5429_);
lean_dec_ref_known(v_fst_5424_, 1);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 0, v_val_5429_);
v___x_5431_ = v___x_5422_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_val_5429_);
v___x_5431_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
return v___x_5431_;
}
}
}
}
else
{
lean_object* v_a_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5441_; 
v_a_5434_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5441_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5441_ == 0)
{
v___x_5436_ = v___x_5419_;
v_isShared_5437_ = v_isSharedCheck_5441_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_a_5434_);
lean_dec(v___x_5419_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5441_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v___x_5439_; 
if (v_isShared_5437_ == 0)
{
v___x_5439_ = v___x_5436_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_a_5434_);
v___x_5439_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5438_;
}
v_reusejp_5438_:
{
return v___x_5439_;
}
}
}
}
}
}
else
{
lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5450_; 
v_a_5443_ = lean_ctor_get(v___x_5405_, 0);
v_isSharedCheck_5450_ = !lean_is_exclusive(v___x_5405_);
if (v_isSharedCheck_5450_ == 0)
{
v___x_5445_ = v___x_5405_;
v_isShared_5446_ = v_isSharedCheck_5450_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_a_5443_);
lean_dec(v___x_5405_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5450_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v___x_5448_; 
if (v_isShared_5446_ == 0)
{
v___x_5448_ = v___x_5445_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_a_5443_);
v___x_5448_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
return v___x_5448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5451_, lean_object* v_init_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5451_, v_init_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec(v___y_5453_);
lean_dec_ref(v_t_5451_);
return v_res_5463_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; 
v___x_5464_ = lean_unsigned_to_nat(32u);
v___x_5465_ = lean_mk_empty_array_with_capacity(v___x_5464_);
v___x_5466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5466_, 0, v___x_5465_);
return v___x_5466_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v_result_5472_; 
v___x_5467_ = ((size_t)5ULL);
v___x_5468_ = lean_unsigned_to_nat(0u);
v___x_5469_ = lean_unsigned_to_nat(32u);
v___x_5470_ = lean_mk_empty_array_with_capacity(v___x_5469_);
v___x_5471_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5472_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5472_, 0, v___x_5471_);
lean_ctor_set(v_result_5472_, 1, v___x_5470_);
lean_ctor_set(v_result_5472_, 2, v___x_5468_);
lean_ctor_set(v_result_5472_, 3, v___x_5468_);
lean_ctor_set_usize(v_result_5472_, 4, v___x_5467_);
return v_result_5472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_){
_start:
{
lean_object* v_result_5484_; lean_object* v___x_5485_; 
v_result_5484_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5485_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5473_, v_result_5484_, v_a_5474_, v_a_5475_, v_a_5476_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_);
return v___x_5485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_, lean_object* v_a_5489_, lean_object* v_a_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_){
_start:
{
lean_object* v_res_5497_; 
v_res_5497_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5486_, v_a_5487_, v_a_5488_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_, v_a_5493_, v_a_5494_, v_a_5495_);
lean_dec(v_a_5495_);
lean_dec_ref(v_a_5494_);
lean_dec(v_a_5493_);
lean_dec_ref(v_a_5492_);
lean_dec(v_a_5491_);
lean_dec_ref(v_a_5490_);
lean_dec(v_a_5489_);
lean_dec_ref(v_a_5488_);
lean_dec(v_a_5487_);
lean_dec_ref(v_thms_5486_);
return v_res_5497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_5500_, lean_object* v_newThms_5501_, lean_object* v_gmt_5502_, lean_object* v_numInstances_5503_, lean_object* v_numDelayedInstances_5504_, lean_object* v_num_5505_, lean_object* v_preInstances_5506_, lean_object* v_nextThmIdx_5507_, lean_object* v_matchEqNames_5508_, lean_object* v_delayedThmInsts_5509_, lean_object* v_nextDeclIdx_5510_, lean_object* v_enodeMap_5511_, lean_object* v_exprs_5512_, lean_object* v_parents_5513_, lean_object* v_congrTable_5514_, lean_object* v_appMap_5515_, lean_object* v_indicesFound_5516_, lean_object* v_newFacts_5517_, uint8_t v_inconsistent_5518_, lean_object* v_nextIdx_5519_, lean_object* v_newRawFacts_5520_, lean_object* v_facts_5521_, lean_object* v_extThms_5522_, lean_object* v_inj_5523_, lean_object* v_split_5524_, lean_object* v_clean_5525_, lean_object* v_sstates_5526_, lean_object* v_mvarId_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_){
_start:
{
lean_object* v___x_5538_; 
v___x_5538_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5500_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_);
if (lean_obj_tag(v___x_5538_) == 0)
{
lean_object* v_a_5539_; lean_object* v___x_5540_; 
v_a_5539_ = lean_ctor_get(v___x_5538_, 0);
lean_inc(v_a_5539_);
lean_dec_ref_known(v___x_5538_, 1);
v___x_5540_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_5501_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_);
if (lean_obj_tag(v___x_5540_) == 0)
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5552_; 
v_a_5541_ = lean_ctor_get(v___x_5540_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5540_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5543_ = v___x_5540_;
v_isShared_5544_ = v_isSharedCheck_5552_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5540_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5552_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5550_; 
v___x_5545_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_5546_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5546_, 0, v___x_5545_);
lean_ctor_set(v___x_5546_, 1, v_gmt_5502_);
lean_ctor_set(v___x_5546_, 2, v_a_5539_);
lean_ctor_set(v___x_5546_, 3, v_a_5541_);
lean_ctor_set(v___x_5546_, 4, v_numInstances_5503_);
lean_ctor_set(v___x_5546_, 5, v_numDelayedInstances_5504_);
lean_ctor_set(v___x_5546_, 6, v_num_5505_);
lean_ctor_set(v___x_5546_, 7, v_preInstances_5506_);
lean_ctor_set(v___x_5546_, 8, v_nextThmIdx_5507_);
lean_ctor_set(v___x_5546_, 9, v_matchEqNames_5508_);
lean_ctor_set(v___x_5546_, 10, v_delayedThmInsts_5509_);
v___x_5547_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_5547_, 0, v_nextDeclIdx_5510_);
lean_ctor_set(v___x_5547_, 1, v_enodeMap_5511_);
lean_ctor_set(v___x_5547_, 2, v_exprs_5512_);
lean_ctor_set(v___x_5547_, 3, v_parents_5513_);
lean_ctor_set(v___x_5547_, 4, v_congrTable_5514_);
lean_ctor_set(v___x_5547_, 5, v_appMap_5515_);
lean_ctor_set(v___x_5547_, 6, v_indicesFound_5516_);
lean_ctor_set(v___x_5547_, 7, v_newFacts_5517_);
lean_ctor_set(v___x_5547_, 8, v_nextIdx_5519_);
lean_ctor_set(v___x_5547_, 9, v_newRawFacts_5520_);
lean_ctor_set(v___x_5547_, 10, v_facts_5521_);
lean_ctor_set(v___x_5547_, 11, v_extThms_5522_);
lean_ctor_set(v___x_5547_, 12, v___x_5546_);
lean_ctor_set(v___x_5547_, 13, v_inj_5523_);
lean_ctor_set(v___x_5547_, 14, v_split_5524_);
lean_ctor_set(v___x_5547_, 15, v_clean_5525_);
lean_ctor_set(v___x_5547_, 16, v_sstates_5526_);
lean_ctor_set_uint8(v___x_5547_, sizeof(void*)*17, v_inconsistent_5518_);
v___x_5548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5548_, 0, v___x_5547_);
lean_ctor_set(v___x_5548_, 1, v_mvarId_5527_);
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 0, v___x_5548_);
v___x_5550_ = v___x_5543_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v___x_5548_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
}
else
{
lean_object* v_a_5553_; lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5560_; 
lean_dec(v_a_5539_);
lean_dec(v_mvarId_5527_);
lean_dec_ref(v_sstates_5526_);
lean_dec_ref(v_clean_5525_);
lean_dec_ref(v_split_5524_);
lean_dec_ref(v_inj_5523_);
lean_dec_ref(v_extThms_5522_);
lean_dec_ref(v_facts_5521_);
lean_dec_ref(v_newRawFacts_5520_);
lean_dec(v_nextIdx_5519_);
lean_dec_ref(v_newFacts_5517_);
lean_dec_ref(v_indicesFound_5516_);
lean_dec_ref(v_appMap_5515_);
lean_dec_ref(v_congrTable_5514_);
lean_dec_ref(v_parents_5513_);
lean_dec_ref(v_exprs_5512_);
lean_dec_ref(v_enodeMap_5511_);
lean_dec(v_nextDeclIdx_5510_);
lean_dec_ref(v_delayedThmInsts_5509_);
lean_dec_ref(v_matchEqNames_5508_);
lean_dec(v_nextThmIdx_5507_);
lean_dec_ref(v_preInstances_5506_);
lean_dec(v_num_5505_);
lean_dec(v_numDelayedInstances_5504_);
lean_dec(v_numInstances_5503_);
lean_dec(v_gmt_5502_);
v_a_5553_ = lean_ctor_get(v___x_5540_, 0);
v_isSharedCheck_5560_ = !lean_is_exclusive(v___x_5540_);
if (v_isSharedCheck_5560_ == 0)
{
v___x_5555_ = v___x_5540_;
v_isShared_5556_ = v_isSharedCheck_5560_;
goto v_resetjp_5554_;
}
else
{
lean_inc(v_a_5553_);
lean_dec(v___x_5540_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5560_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v___x_5558_; 
if (v_isShared_5556_ == 0)
{
v___x_5558_ = v___x_5555_;
goto v_reusejp_5557_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v_a_5553_);
v___x_5558_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5557_;
}
v_reusejp_5557_:
{
return v___x_5558_;
}
}
}
}
else
{
lean_object* v_a_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5568_; 
lean_dec(v_mvarId_5527_);
lean_dec_ref(v_sstates_5526_);
lean_dec_ref(v_clean_5525_);
lean_dec_ref(v_split_5524_);
lean_dec_ref(v_inj_5523_);
lean_dec_ref(v_extThms_5522_);
lean_dec_ref(v_facts_5521_);
lean_dec_ref(v_newRawFacts_5520_);
lean_dec(v_nextIdx_5519_);
lean_dec_ref(v_newFacts_5517_);
lean_dec_ref(v_indicesFound_5516_);
lean_dec_ref(v_appMap_5515_);
lean_dec_ref(v_congrTable_5514_);
lean_dec_ref(v_parents_5513_);
lean_dec_ref(v_exprs_5512_);
lean_dec_ref(v_enodeMap_5511_);
lean_dec(v_nextDeclIdx_5510_);
lean_dec_ref(v_delayedThmInsts_5509_);
lean_dec_ref(v_matchEqNames_5508_);
lean_dec(v_nextThmIdx_5507_);
lean_dec_ref(v_preInstances_5506_);
lean_dec(v_num_5505_);
lean_dec(v_numDelayedInstances_5504_);
lean_dec(v_numInstances_5503_);
lean_dec(v_gmt_5502_);
v_a_5561_ = lean_ctor_get(v___x_5538_, 0);
v_isSharedCheck_5568_ = !lean_is_exclusive(v___x_5538_);
if (v_isSharedCheck_5568_ == 0)
{
v___x_5563_ = v___x_5538_;
v_isShared_5564_ = v_isSharedCheck_5568_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_a_5561_);
lean_dec(v___x_5538_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5568_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5566_; 
if (v_isShared_5564_ == 0)
{
v___x_5566_ = v___x_5563_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_a_5561_);
v___x_5566_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
return v___x_5566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_5569_ = _args[0];
lean_object* v_newThms_5570_ = _args[1];
lean_object* v_gmt_5571_ = _args[2];
lean_object* v_numInstances_5572_ = _args[3];
lean_object* v_numDelayedInstances_5573_ = _args[4];
lean_object* v_num_5574_ = _args[5];
lean_object* v_preInstances_5575_ = _args[6];
lean_object* v_nextThmIdx_5576_ = _args[7];
lean_object* v_matchEqNames_5577_ = _args[8];
lean_object* v_delayedThmInsts_5578_ = _args[9];
lean_object* v_nextDeclIdx_5579_ = _args[10];
lean_object* v_enodeMap_5580_ = _args[11];
lean_object* v_exprs_5581_ = _args[12];
lean_object* v_parents_5582_ = _args[13];
lean_object* v_congrTable_5583_ = _args[14];
lean_object* v_appMap_5584_ = _args[15];
lean_object* v_indicesFound_5585_ = _args[16];
lean_object* v_newFacts_5586_ = _args[17];
lean_object* v_inconsistent_5587_ = _args[18];
lean_object* v_nextIdx_5588_ = _args[19];
lean_object* v_newRawFacts_5589_ = _args[20];
lean_object* v_facts_5590_ = _args[21];
lean_object* v_extThms_5591_ = _args[22];
lean_object* v_inj_5592_ = _args[23];
lean_object* v_split_5593_ = _args[24];
lean_object* v_clean_5594_ = _args[25];
lean_object* v_sstates_5595_ = _args[26];
lean_object* v_mvarId_5596_ = _args[27];
lean_object* v___y_5597_ = _args[28];
lean_object* v___y_5598_ = _args[29];
lean_object* v___y_5599_ = _args[30];
lean_object* v___y_5600_ = _args[31];
lean_object* v___y_5601_ = _args[32];
lean_object* v___y_5602_ = _args[33];
lean_object* v___y_5603_ = _args[34];
lean_object* v___y_5604_ = _args[35];
lean_object* v___y_5605_ = _args[36];
lean_object* v___y_5606_ = _args[37];
_start:
{
uint8_t v_inconsistent_boxed_5607_; lean_object* v_res_5608_; 
v_inconsistent_boxed_5607_ = lean_unbox(v_inconsistent_5587_);
v_res_5608_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5569_, v_newThms_5570_, v_gmt_5571_, v_numInstances_5572_, v_numDelayedInstances_5573_, v_num_5574_, v_preInstances_5575_, v_nextThmIdx_5576_, v_matchEqNames_5577_, v_delayedThmInsts_5578_, v_nextDeclIdx_5579_, v_enodeMap_5580_, v_exprs_5581_, v_parents_5582_, v_congrTable_5583_, v_appMap_5584_, v_indicesFound_5585_, v_newFacts_5586_, v_inconsistent_boxed_5607_, v_nextIdx_5588_, v_newRawFacts_5589_, v_facts_5590_, v_extThms_5591_, v_inj_5592_, v_split_5593_, v_clean_5594_, v_sstates_5595_, v_mvarId_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_);
lean_dec(v___y_5605_);
lean_dec_ref(v___y_5604_);
lean_dec(v___y_5603_);
lean_dec_ref(v___y_5602_);
lean_dec(v___y_5601_);
lean_dec_ref(v___y_5600_);
lean_dec(v___y_5599_);
lean_dec_ref(v___y_5598_);
lean_dec(v___y_5597_);
lean_dec_ref(v_newThms_5570_);
lean_dec_ref(v_thms_5569_);
return v_res_5608_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5609_; 
v___x_5609_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_5609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_5610_, size_t v_i_5611_, lean_object* v_bs_5612_){
_start:
{
uint8_t v___x_5613_; 
v___x_5613_ = lean_usize_dec_lt(v_i_5611_, v_sz_5610_);
if (v___x_5613_ == 0)
{
return v_bs_5612_;
}
else
{
lean_object* v_v_5614_; lean_object* v_casesTypes_5615_; lean_object* v_extThms_5616_; lean_object* v_funCC_5617_; lean_object* v_inj_5618_; lean_object* v___x_5620_; uint8_t v_isShared_5621_; uint8_t v_isSharedCheck_5632_; 
v_v_5614_ = lean_array_uget(v_bs_5612_, v_i_5611_);
v_casesTypes_5615_ = lean_ctor_get(v_v_5614_, 0);
v_extThms_5616_ = lean_ctor_get(v_v_5614_, 1);
v_funCC_5617_ = lean_ctor_get(v_v_5614_, 2);
v_inj_5618_ = lean_ctor_get(v_v_5614_, 4);
v_isSharedCheck_5632_ = !lean_is_exclusive(v_v_5614_);
if (v_isSharedCheck_5632_ == 0)
{
lean_object* v_unused_5633_; 
v_unused_5633_ = lean_ctor_get(v_v_5614_, 3);
lean_dec(v_unused_5633_);
v___x_5620_ = v_v_5614_;
v_isShared_5621_ = v_isSharedCheck_5632_;
goto v_resetjp_5619_;
}
else
{
lean_inc(v_inj_5618_);
lean_inc(v_funCC_5617_);
lean_inc(v_extThms_5616_);
lean_inc(v_casesTypes_5615_);
lean_dec(v_v_5614_);
v___x_5620_ = lean_box(0);
v_isShared_5621_ = v_isSharedCheck_5632_;
goto v_resetjp_5619_;
}
v_resetjp_5619_:
{
lean_object* v___x_5622_; lean_object* v_bs_x27_5623_; lean_object* v___x_5624_; lean_object* v___x_5626_; 
v___x_5622_ = lean_unsigned_to_nat(0u);
v_bs_x27_5623_ = lean_array_uset(v_bs_5612_, v_i_5611_, v___x_5622_);
v___x_5624_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_5621_ == 0)
{
lean_ctor_set(v___x_5620_, 3, v___x_5624_);
v___x_5626_ = v___x_5620_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v_casesTypes_5615_);
lean_ctor_set(v_reuseFailAlloc_5631_, 1, v_extThms_5616_);
lean_ctor_set(v_reuseFailAlloc_5631_, 2, v_funCC_5617_);
lean_ctor_set(v_reuseFailAlloc_5631_, 3, v___x_5624_);
lean_ctor_set(v_reuseFailAlloc_5631_, 4, v_inj_5618_);
v___x_5626_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
size_t v___x_5627_; size_t v___x_5628_; lean_object* v___x_5629_; 
v___x_5627_ = ((size_t)1ULL);
v___x_5628_ = lean_usize_add(v_i_5611_, v___x_5627_);
v___x_5629_ = lean_array_uset(v_bs_x27_5623_, v_i_5611_, v___x_5626_);
v_i_5611_ = v___x_5628_;
v_bs_5612_ = v___x_5629_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_5634_, lean_object* v_i_5635_, lean_object* v_bs_5636_){
_start:
{
size_t v_sz_boxed_5637_; size_t v_i_boxed_5638_; lean_object* v_res_5639_; 
v_sz_boxed_5637_ = lean_unbox_usize(v_sz_5634_);
lean_dec(v_sz_5634_);
v_i_boxed_5638_ = lean_unbox_usize(v_i_5635_);
lean_dec(v_i_5635_);
v_res_5639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_5637_, v_i_boxed_5638_, v_bs_5636_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_5640_, lean_object* v_ps_5641_, uint8_t v_only_5642_, lean_object* v_k_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_){
_start:
{
lean_object* v___y_5654_; lean_object* v___y_5655_; lean_object* v___y_5656_; lean_object* v___y_5657_; lean_object* v___y_5658_; lean_object* v___y_5659_; lean_object* v___y_5660_; lean_object* v___y_5661_; lean_object* v___y_5662_; uint8_t v___y_5675_; uint8_t v___y_5676_; lean_object* v_params_5677_; lean_object* v___y_5678_; lean_object* v___y_5679_; lean_object* v___y_5680_; lean_object* v___y_5681_; lean_object* v___y_5682_; lean_object* v___y_5683_; lean_object* v___y_5684_; lean_object* v___y_5685_; uint8_t v___y_5786_; uint8_t v___x_5809_; 
v___x_5809_ = lean_bool_not(v_only_5642_);
if (v___x_5809_ == 0)
{
v___y_5786_ = v___x_5809_;
goto v___jp_5785_;
}
else
{
lean_object* v___x_5810_; lean_object* v___x_5811_; uint8_t v___x_5812_; 
v___x_5810_ = lean_array_get_size(v_ps_5641_);
v___x_5811_ = lean_unsigned_to_nat(0u);
v___x_5812_ = lean_nat_dec_eq(v___x_5810_, v___x_5811_);
v___y_5786_ = v___x_5812_;
goto v___jp_5785_;
}
v___jp_5653_:
{
lean_object* v___x_5663_; lean_object* v___x_5664_; 
v___x_5663_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_5663_, 0, v___y_5654_);
v___x_5664_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_5663_, v___y_5655_, v___y_5656_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_);
if (lean_obj_tag(v___x_5664_) == 0)
{
lean_object* v___x_5665_; 
lean_dec_ref_known(v___x_5664_, 1);
lean_inc(v___y_5662_);
lean_inc_ref(v___y_5661_);
lean_inc(v___y_5660_);
lean_inc_ref(v___y_5659_);
lean_inc(v___y_5658_);
lean_inc_ref(v___y_5657_);
lean_inc(v___y_5656_);
v___x_5665_ = lean_apply_9(v_k_5643_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_, lean_box(0));
return v___x_5665_;
}
else
{
lean_object* v_a_5666_; lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5673_; 
lean_dec_ref(v___y_5655_);
lean_dec_ref(v_k_5643_);
v_a_5666_ = lean_ctor_get(v___x_5664_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5664_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5668_ = v___x_5664_;
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
else
{
lean_inc(v_a_5666_);
lean_dec(v___x_5664_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5671_; 
if (v_isShared_5669_ == 0)
{
v___x_5671_ = v___x_5668_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_a_5666_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
}
v___jp_5674_:
{
lean_object* v___x_5686_; 
v___x_5686_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5677_, v_ps_5641_, v_only_5642_, v___y_5675_, v___y_5676_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
if (lean_obj_tag(v___x_5686_) == 0)
{
lean_object* v_a_5687_; lean_object* v_ctx_5688_; lean_object* v_anchorRefs_x3f_5689_; lean_object* v_toContext_5690_; lean_object* v_sctx_5691_; lean_object* v_methods_5692_; uint8_t v_sym_5693_; lean_object* v_simp_5694_; lean_object* v_simpMethods_5695_; lean_object* v_config_5696_; uint8_t v_cheapCases_5697_; uint8_t v_reportMVarIssue_5698_; lean_object* v_splitSource_5699_; lean_object* v_ematchDiagSource_5700_; lean_object* v_symPrios_5701_; lean_object* v_extensions_5702_; uint8_t v_debug_5703_; uint8_t v_ematchDiag_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; 
v_a_5687_ = lean_ctor_get(v___x_5686_, 0);
lean_inc_n(v_a_5687_, 2);
lean_dec_ref_known(v___x_5686_, 1);
v_ctx_5688_ = lean_ctor_get(v___y_5678_, 1);
v_anchorRefs_x3f_5689_ = lean_ctor_get(v_a_5687_, 8);
v_toContext_5690_ = lean_ctor_get(v___y_5678_, 0);
v_sctx_5691_ = lean_ctor_get(v___y_5678_, 2);
v_methods_5692_ = lean_ctor_get(v___y_5678_, 3);
v_sym_5693_ = lean_ctor_get_uint8(v___y_5678_, sizeof(void*)*5);
v_simp_5694_ = lean_ctor_get(v_ctx_5688_, 0);
v_simpMethods_5695_ = lean_ctor_get(v_ctx_5688_, 1);
v_config_5696_ = lean_ctor_get(v_ctx_5688_, 2);
v_cheapCases_5697_ = lean_ctor_get_uint8(v_ctx_5688_, sizeof(void*)*8);
v_reportMVarIssue_5698_ = lean_ctor_get_uint8(v_ctx_5688_, sizeof(void*)*8 + 1);
v_splitSource_5699_ = lean_ctor_get(v_ctx_5688_, 4);
v_ematchDiagSource_5700_ = lean_ctor_get(v_ctx_5688_, 5);
v_symPrios_5701_ = lean_ctor_get(v_ctx_5688_, 6);
v_extensions_5702_ = lean_ctor_get(v_ctx_5688_, 7);
v_debug_5703_ = lean_ctor_get_uint8(v_ctx_5688_, sizeof(void*)*8 + 2);
v_ematchDiag_5704_ = lean_ctor_get_uint8(v_ctx_5688_, sizeof(void*)*8 + 3);
lean_inc_ref(v_extensions_5702_);
lean_inc_ref(v_symPrios_5701_);
lean_inc(v_ematchDiagSource_5700_);
lean_inc(v_splitSource_5699_);
lean_inc(v_anchorRefs_x3f_5689_);
lean_inc_ref(v_config_5696_);
lean_inc_ref(v_simpMethods_5695_);
lean_inc_ref(v_simp_5694_);
v___x_5705_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_5705_, 0, v_simp_5694_);
lean_ctor_set(v___x_5705_, 1, v_simpMethods_5695_);
lean_ctor_set(v___x_5705_, 2, v_config_5696_);
lean_ctor_set(v___x_5705_, 3, v_anchorRefs_x3f_5689_);
lean_ctor_set(v___x_5705_, 4, v_splitSource_5699_);
lean_ctor_set(v___x_5705_, 5, v_ematchDiagSource_5700_);
lean_ctor_set(v___x_5705_, 6, v_symPrios_5701_);
lean_ctor_set(v___x_5705_, 7, v_extensions_5702_);
lean_ctor_set_uint8(v___x_5705_, sizeof(void*)*8, v_cheapCases_5697_);
lean_ctor_set_uint8(v___x_5705_, sizeof(void*)*8 + 1, v_reportMVarIssue_5698_);
lean_ctor_set_uint8(v___x_5705_, sizeof(void*)*8 + 2, v_debug_5703_);
lean_ctor_set_uint8(v___x_5705_, sizeof(void*)*8 + 3, v_ematchDiag_5704_);
lean_inc_ref(v_methods_5692_);
lean_inc_ref(v_sctx_5691_);
lean_inc_ref(v_toContext_5690_);
v___x_5706_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_5706_, 0, v_toContext_5690_);
lean_ctor_set(v___x_5706_, 1, v___x_5705_);
lean_ctor_set(v___x_5706_, 2, v_sctx_5691_);
lean_ctor_set(v___x_5706_, 3, v_methods_5692_);
lean_ctor_set(v___x_5706_, 4, v_a_5687_);
lean_ctor_set_uint8(v___x_5706_, sizeof(void*)*5, v_sym_5693_);
if (v_only_5642_ == 0)
{
v___y_5654_ = v_a_5687_;
v___y_5655_ = v___x_5706_;
v___y_5656_ = v___y_5679_;
v___y_5657_ = v___y_5680_;
v___y_5658_ = v___y_5681_;
v___y_5659_ = v___y_5682_;
v___y_5660_ = v___y_5683_;
v___y_5661_ = v___y_5684_;
v___y_5662_ = v___y_5685_;
goto v___jp_5653_;
}
else
{
lean_object* v___x_5707_; 
v___x_5707_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_5679_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
if (lean_obj_tag(v___x_5707_) == 0)
{
lean_object* v_a_5708_; lean_object* v_toGoalState_5709_; lean_object* v_ematch_5710_; lean_object* v_mvarId_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5767_; 
v_a_5708_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_a_5708_);
lean_dec_ref_known(v___x_5707_, 1);
v_toGoalState_5709_ = lean_ctor_get(v_a_5708_, 0);
lean_inc_ref(v_toGoalState_5709_);
v_ematch_5710_ = lean_ctor_get(v_toGoalState_5709_, 12);
lean_inc_ref(v_ematch_5710_);
v_mvarId_5711_ = lean_ctor_get(v_a_5708_, 1);
v_isSharedCheck_5767_ = !lean_is_exclusive(v_a_5708_);
if (v_isSharedCheck_5767_ == 0)
{
lean_object* v_unused_5768_; 
v_unused_5768_ = lean_ctor_get(v_a_5708_, 0);
lean_dec(v_unused_5768_);
v___x_5713_ = v_a_5708_;
v_isShared_5714_ = v_isSharedCheck_5767_;
goto v_resetjp_5712_;
}
else
{
lean_inc(v_mvarId_5711_);
lean_dec(v_a_5708_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5767_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v_nextDeclIdx_5715_; lean_object* v_enodeMap_5716_; lean_object* v_exprs_5717_; lean_object* v_parents_5718_; lean_object* v_congrTable_5719_; lean_object* v_appMap_5720_; lean_object* v_indicesFound_5721_; lean_object* v_newFacts_5722_; uint8_t v_inconsistent_5723_; lean_object* v_nextIdx_5724_; lean_object* v_newRawFacts_5725_; lean_object* v_facts_5726_; lean_object* v_extThms_5727_; lean_object* v_inj_5728_; lean_object* v_split_5729_; lean_object* v_clean_5730_; lean_object* v_sstates_5731_; lean_object* v_gmt_5732_; lean_object* v_thms_5733_; lean_object* v_newThms_5734_; lean_object* v_numInstances_5735_; lean_object* v_numDelayedInstances_5736_; lean_object* v_num_5737_; lean_object* v_preInstances_5738_; lean_object* v_nextThmIdx_5739_; lean_object* v_matchEqNames_5740_; lean_object* v_delayedThmInsts_5741_; lean_object* v___x_5742_; lean_object* v___f_5743_; lean_object* v___x_5744_; 
v_nextDeclIdx_5715_ = lean_ctor_get(v_toGoalState_5709_, 0);
lean_inc(v_nextDeclIdx_5715_);
v_enodeMap_5716_ = lean_ctor_get(v_toGoalState_5709_, 1);
lean_inc_ref(v_enodeMap_5716_);
v_exprs_5717_ = lean_ctor_get(v_toGoalState_5709_, 2);
lean_inc_ref(v_exprs_5717_);
v_parents_5718_ = lean_ctor_get(v_toGoalState_5709_, 3);
lean_inc_ref(v_parents_5718_);
v_congrTable_5719_ = lean_ctor_get(v_toGoalState_5709_, 4);
lean_inc_ref(v_congrTable_5719_);
v_appMap_5720_ = lean_ctor_get(v_toGoalState_5709_, 5);
lean_inc_ref(v_appMap_5720_);
v_indicesFound_5721_ = lean_ctor_get(v_toGoalState_5709_, 6);
lean_inc_ref(v_indicesFound_5721_);
v_newFacts_5722_ = lean_ctor_get(v_toGoalState_5709_, 7);
lean_inc_ref(v_newFacts_5722_);
v_inconsistent_5723_ = lean_ctor_get_uint8(v_toGoalState_5709_, sizeof(void*)*17);
v_nextIdx_5724_ = lean_ctor_get(v_toGoalState_5709_, 8);
lean_inc(v_nextIdx_5724_);
v_newRawFacts_5725_ = lean_ctor_get(v_toGoalState_5709_, 9);
lean_inc_ref(v_newRawFacts_5725_);
v_facts_5726_ = lean_ctor_get(v_toGoalState_5709_, 10);
lean_inc_ref(v_facts_5726_);
v_extThms_5727_ = lean_ctor_get(v_toGoalState_5709_, 11);
lean_inc_ref(v_extThms_5727_);
v_inj_5728_ = lean_ctor_get(v_toGoalState_5709_, 13);
lean_inc_ref(v_inj_5728_);
v_split_5729_ = lean_ctor_get(v_toGoalState_5709_, 14);
lean_inc_ref(v_split_5729_);
v_clean_5730_ = lean_ctor_get(v_toGoalState_5709_, 15);
lean_inc_ref(v_clean_5730_);
v_sstates_5731_ = lean_ctor_get(v_toGoalState_5709_, 16);
lean_inc_ref(v_sstates_5731_);
lean_dec_ref(v_toGoalState_5709_);
v_gmt_5732_ = lean_ctor_get(v_ematch_5710_, 1);
lean_inc(v_gmt_5732_);
v_thms_5733_ = lean_ctor_get(v_ematch_5710_, 2);
lean_inc_ref(v_thms_5733_);
v_newThms_5734_ = lean_ctor_get(v_ematch_5710_, 3);
lean_inc_ref(v_newThms_5734_);
v_numInstances_5735_ = lean_ctor_get(v_ematch_5710_, 4);
lean_inc(v_numInstances_5735_);
v_numDelayedInstances_5736_ = lean_ctor_get(v_ematch_5710_, 5);
lean_inc(v_numDelayedInstances_5736_);
v_num_5737_ = lean_ctor_get(v_ematch_5710_, 6);
lean_inc(v_num_5737_);
v_preInstances_5738_ = lean_ctor_get(v_ematch_5710_, 7);
lean_inc_ref(v_preInstances_5738_);
v_nextThmIdx_5739_ = lean_ctor_get(v_ematch_5710_, 8);
lean_inc(v_nextThmIdx_5739_);
v_matchEqNames_5740_ = lean_ctor_get(v_ematch_5710_, 9);
lean_inc_ref(v_matchEqNames_5740_);
v_delayedThmInsts_5741_ = lean_ctor_get(v_ematch_5710_, 10);
lean_inc_ref(v_delayedThmInsts_5741_);
lean_dec_ref(v_ematch_5710_);
v___x_5742_ = lean_box(v_inconsistent_5723_);
v___f_5743_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 38, 28);
lean_closure_set(v___f_5743_, 0, v_thms_5733_);
lean_closure_set(v___f_5743_, 1, v_newThms_5734_);
lean_closure_set(v___f_5743_, 2, v_gmt_5732_);
lean_closure_set(v___f_5743_, 3, v_numInstances_5735_);
lean_closure_set(v___f_5743_, 4, v_numDelayedInstances_5736_);
lean_closure_set(v___f_5743_, 5, v_num_5737_);
lean_closure_set(v___f_5743_, 6, v_preInstances_5738_);
lean_closure_set(v___f_5743_, 7, v_nextThmIdx_5739_);
lean_closure_set(v___f_5743_, 8, v_matchEqNames_5740_);
lean_closure_set(v___f_5743_, 9, v_delayedThmInsts_5741_);
lean_closure_set(v___f_5743_, 10, v_nextDeclIdx_5715_);
lean_closure_set(v___f_5743_, 11, v_enodeMap_5716_);
lean_closure_set(v___f_5743_, 12, v_exprs_5717_);
lean_closure_set(v___f_5743_, 13, v_parents_5718_);
lean_closure_set(v___f_5743_, 14, v_congrTable_5719_);
lean_closure_set(v___f_5743_, 15, v_appMap_5720_);
lean_closure_set(v___f_5743_, 16, v_indicesFound_5721_);
lean_closure_set(v___f_5743_, 17, v_newFacts_5722_);
lean_closure_set(v___f_5743_, 18, v___x_5742_);
lean_closure_set(v___f_5743_, 19, v_nextIdx_5724_);
lean_closure_set(v___f_5743_, 20, v_newRawFacts_5725_);
lean_closure_set(v___f_5743_, 21, v_facts_5726_);
lean_closure_set(v___f_5743_, 22, v_extThms_5727_);
lean_closure_set(v___f_5743_, 23, v_inj_5728_);
lean_closure_set(v___f_5743_, 24, v_split_5729_);
lean_closure_set(v___f_5743_, 25, v_clean_5730_);
lean_closure_set(v___f_5743_, 26, v_sstates_5731_);
lean_closure_set(v___f_5743_, 27, v_mvarId_5711_);
v___x_5744_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_5743_, v___x_5706_, v___y_5679_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
if (lean_obj_tag(v___x_5744_) == 0)
{
lean_object* v_a_5745_; lean_object* v___x_5746_; lean_object* v___x_5748_; 
v_a_5745_ = lean_ctor_get(v___x_5744_, 0);
lean_inc(v_a_5745_);
lean_dec_ref_known(v___x_5744_, 1);
v___x_5746_ = lean_box(0);
if (v_isShared_5714_ == 0)
{
lean_ctor_set_tag(v___x_5713_, 1);
lean_ctor_set(v___x_5713_, 1, v___x_5746_);
lean_ctor_set(v___x_5713_, 0, v_a_5745_);
v___x_5748_ = v___x_5713_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5758_; 
v_reuseFailAlloc_5758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5758_, 0, v_a_5745_);
lean_ctor_set(v_reuseFailAlloc_5758_, 1, v___x_5746_);
v___x_5748_ = v_reuseFailAlloc_5758_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
lean_object* v___x_5749_; 
v___x_5749_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_5748_, v___y_5679_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
if (lean_obj_tag(v___x_5749_) == 0)
{
lean_dec_ref_known(v___x_5749_, 1);
v___y_5654_ = v_a_5687_;
v___y_5655_ = v___x_5706_;
v___y_5656_ = v___y_5679_;
v___y_5657_ = v___y_5680_;
v___y_5658_ = v___y_5681_;
v___y_5659_ = v___y_5682_;
v___y_5660_ = v___y_5683_;
v___y_5661_ = v___y_5684_;
v___y_5662_ = v___y_5685_;
goto v___jp_5653_;
}
else
{
lean_object* v_a_5750_; lean_object* v___x_5752_; uint8_t v_isShared_5753_; uint8_t v_isSharedCheck_5757_; 
lean_dec_ref_known(v___x_5706_, 5);
lean_dec(v_a_5687_);
lean_dec_ref(v_k_5643_);
v_a_5750_ = lean_ctor_get(v___x_5749_, 0);
v_isSharedCheck_5757_ = !lean_is_exclusive(v___x_5749_);
if (v_isSharedCheck_5757_ == 0)
{
v___x_5752_ = v___x_5749_;
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
else
{
lean_inc(v_a_5750_);
lean_dec(v___x_5749_);
v___x_5752_ = lean_box(0);
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
v_resetjp_5751_:
{
lean_object* v___x_5755_; 
if (v_isShared_5753_ == 0)
{
v___x_5755_ = v___x_5752_;
goto v_reusejp_5754_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_a_5750_);
v___x_5755_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5754_;
}
v_reusejp_5754_:
{
return v___x_5755_;
}
}
}
}
}
else
{
lean_object* v_a_5759_; lean_object* v___x_5761_; uint8_t v_isShared_5762_; uint8_t v_isSharedCheck_5766_; 
lean_del_object(v___x_5713_);
lean_dec_ref_known(v___x_5706_, 5);
lean_dec(v_a_5687_);
lean_dec_ref(v_k_5643_);
v_a_5759_ = lean_ctor_get(v___x_5744_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v___x_5744_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5761_ = v___x_5744_;
v_isShared_5762_ = v_isSharedCheck_5766_;
goto v_resetjp_5760_;
}
else
{
lean_inc(v_a_5759_);
lean_dec(v___x_5744_);
v___x_5761_ = lean_box(0);
v_isShared_5762_ = v_isSharedCheck_5766_;
goto v_resetjp_5760_;
}
v_resetjp_5760_:
{
lean_object* v___x_5764_; 
if (v_isShared_5762_ == 0)
{
v___x_5764_ = v___x_5761_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5759_);
v___x_5764_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
return v___x_5764_;
}
}
}
}
}
else
{
lean_object* v_a_5769_; lean_object* v___x_5771_; uint8_t v_isShared_5772_; uint8_t v_isSharedCheck_5776_; 
lean_dec_ref_known(v___x_5706_, 5);
lean_dec(v_a_5687_);
lean_dec_ref(v_k_5643_);
v_a_5769_ = lean_ctor_get(v___x_5707_, 0);
v_isSharedCheck_5776_ = !lean_is_exclusive(v___x_5707_);
if (v_isSharedCheck_5776_ == 0)
{
v___x_5771_ = v___x_5707_;
v_isShared_5772_ = v_isSharedCheck_5776_;
goto v_resetjp_5770_;
}
else
{
lean_inc(v_a_5769_);
lean_dec(v___x_5707_);
v___x_5771_ = lean_box(0);
v_isShared_5772_ = v_isSharedCheck_5776_;
goto v_resetjp_5770_;
}
v_resetjp_5770_:
{
lean_object* v___x_5774_; 
if (v_isShared_5772_ == 0)
{
v___x_5774_ = v___x_5771_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v_a_5769_);
v___x_5774_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
return v___x_5774_;
}
}
}
}
}
else
{
lean_object* v_a_5777_; lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5784_; 
lean_dec_ref(v_k_5643_);
v_a_5777_ = lean_ctor_get(v___x_5686_, 0);
v_isSharedCheck_5784_ = !lean_is_exclusive(v___x_5686_);
if (v_isSharedCheck_5784_ == 0)
{
v___x_5779_ = v___x_5686_;
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
else
{
lean_inc(v_a_5777_);
lean_dec(v___x_5686_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v___x_5782_; 
if (v_isShared_5780_ == 0)
{
v___x_5782_ = v___x_5779_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_a_5777_);
v___x_5782_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
return v___x_5782_;
}
}
}
}
v___jp_5785_:
{
if (v___y_5786_ == 0)
{
uint8_t v___x_5787_; 
v___x_5787_ = 1;
if (v_only_5642_ == 0)
{
v___y_5675_ = v___y_5786_;
v___y_5676_ = v___x_5787_;
v_params_5677_ = v_params_5640_;
v___y_5678_ = v_a_5644_;
v___y_5679_ = v_a_5645_;
v___y_5680_ = v_a_5646_;
v___y_5681_ = v_a_5647_;
v___y_5682_ = v_a_5648_;
v___y_5683_ = v_a_5649_;
v___y_5684_ = v_a_5650_;
v___y_5685_ = v_a_5651_;
goto v___jp_5674_;
}
else
{
lean_object* v_config_5788_; lean_object* v_extensions_5789_; lean_object* v_extra_5790_; lean_object* v_extraInj_5791_; lean_object* v_extraFacts_5792_; lean_object* v_symPrios_5793_; lean_object* v_norm_5794_; lean_object* v_normProcs_5795_; lean_object* v___x_5797_; uint8_t v_isShared_5798_; uint8_t v_isSharedCheck_5806_; 
v_config_5788_ = lean_ctor_get(v_params_5640_, 0);
v_extensions_5789_ = lean_ctor_get(v_params_5640_, 1);
v_extra_5790_ = lean_ctor_get(v_params_5640_, 2);
v_extraInj_5791_ = lean_ctor_get(v_params_5640_, 3);
v_extraFacts_5792_ = lean_ctor_get(v_params_5640_, 4);
v_symPrios_5793_ = lean_ctor_get(v_params_5640_, 5);
v_norm_5794_ = lean_ctor_get(v_params_5640_, 6);
v_normProcs_5795_ = lean_ctor_get(v_params_5640_, 7);
v_isSharedCheck_5806_ = !lean_is_exclusive(v_params_5640_);
if (v_isSharedCheck_5806_ == 0)
{
lean_object* v_unused_5807_; 
v_unused_5807_ = lean_ctor_get(v_params_5640_, 8);
lean_dec(v_unused_5807_);
v___x_5797_ = v_params_5640_;
v_isShared_5798_ = v_isSharedCheck_5806_;
goto v_resetjp_5796_;
}
else
{
lean_inc(v_normProcs_5795_);
lean_inc(v_norm_5794_);
lean_inc(v_symPrios_5793_);
lean_inc(v_extraFacts_5792_);
lean_inc(v_extraInj_5791_);
lean_inc(v_extra_5790_);
lean_inc(v_extensions_5789_);
lean_inc(v_config_5788_);
lean_dec(v_params_5640_);
v___x_5797_ = lean_box(0);
v_isShared_5798_ = v_isSharedCheck_5806_;
goto v_resetjp_5796_;
}
v_resetjp_5796_:
{
size_t v_sz_5799_; size_t v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v_params_5804_; 
v_sz_5799_ = lean_array_size(v_extensions_5789_);
v___x_5800_ = ((size_t)0ULL);
v___x_5801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_5799_, v___x_5800_, v_extensions_5789_);
v___x_5802_ = lean_box(0);
if (v_isShared_5798_ == 0)
{
lean_ctor_set(v___x_5797_, 8, v___x_5802_);
lean_ctor_set(v___x_5797_, 1, v___x_5801_);
v_params_5804_ = v___x_5797_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v_config_5788_);
lean_ctor_set(v_reuseFailAlloc_5805_, 1, v___x_5801_);
lean_ctor_set(v_reuseFailAlloc_5805_, 2, v_extra_5790_);
lean_ctor_set(v_reuseFailAlloc_5805_, 3, v_extraInj_5791_);
lean_ctor_set(v_reuseFailAlloc_5805_, 4, v_extraFacts_5792_);
lean_ctor_set(v_reuseFailAlloc_5805_, 5, v_symPrios_5793_);
lean_ctor_set(v_reuseFailAlloc_5805_, 6, v_norm_5794_);
lean_ctor_set(v_reuseFailAlloc_5805_, 7, v_normProcs_5795_);
lean_ctor_set(v_reuseFailAlloc_5805_, 8, v___x_5802_);
v_params_5804_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
v___y_5675_ = v___y_5786_;
v___y_5676_ = v___x_5787_;
v_params_5677_ = v_params_5804_;
v___y_5678_ = v_a_5644_;
v___y_5679_ = v_a_5645_;
v___y_5680_ = v_a_5646_;
v___y_5681_ = v_a_5647_;
v___y_5682_ = v_a_5648_;
v___y_5683_ = v_a_5649_;
v___y_5684_ = v_a_5650_;
v___y_5685_ = v_a_5651_;
goto v___jp_5674_;
}
}
}
}
else
{
lean_object* v___x_5808_; 
lean_dec_ref(v_params_5640_);
lean_inc(v_a_5651_);
lean_inc_ref(v_a_5650_);
lean_inc(v_a_5649_);
lean_inc_ref(v_a_5648_);
lean_inc(v_a_5647_);
lean_inc_ref(v_a_5646_);
lean_inc(v_a_5645_);
lean_inc_ref(v_a_5644_);
v___x_5808_ = lean_apply_9(v_k_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, lean_box(0));
return v___x_5808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_5813_, lean_object* v_ps_5814_, lean_object* v_only_5815_, lean_object* v_k_5816_, lean_object* v_a_5817_, lean_object* v_a_5818_, lean_object* v_a_5819_, lean_object* v_a_5820_, lean_object* v_a_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_){
_start:
{
uint8_t v_only_boxed_5826_; lean_object* v_res_5827_; 
v_only_boxed_5826_ = lean_unbox(v_only_5815_);
v_res_5827_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5813_, v_ps_5814_, v_only_boxed_5826_, v_k_5816_, v_a_5817_, v_a_5818_, v_a_5819_, v_a_5820_, v_a_5821_, v_a_5822_, v_a_5823_, v_a_5824_);
lean_dec(v_a_5824_);
lean_dec_ref(v_a_5823_);
lean_dec(v_a_5822_);
lean_dec_ref(v_a_5821_);
lean_dec(v_a_5820_);
lean_dec_ref(v_a_5819_);
lean_dec(v_a_5818_);
lean_dec_ref(v_a_5817_);
lean_dec_ref(v_ps_5814_);
return v_res_5827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_5828_, lean_object* v_params_5829_, lean_object* v_ps_5830_, uint8_t v_only_5831_, lean_object* v_k_5832_, lean_object* v_a_5833_, lean_object* v_a_5834_, lean_object* v_a_5835_, lean_object* v_a_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_){
_start:
{
lean_object* v___x_5842_; 
v___x_5842_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5829_, v_ps_5830_, v_only_5831_, v_k_5832_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_);
return v___x_5842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_5843_, lean_object* v_params_5844_, lean_object* v_ps_5845_, lean_object* v_only_5846_, lean_object* v_k_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_){
_start:
{
uint8_t v_only_boxed_5857_; lean_object* v_res_5858_; 
v_only_boxed_5857_ = lean_unbox(v_only_5846_);
v_res_5858_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_5843_, v_params_5844_, v_ps_5845_, v_only_boxed_5857_, v_k_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_);
lean_dec(v_a_5855_);
lean_dec_ref(v_a_5854_);
lean_dec(v_a_5853_);
lean_dec_ref(v_a_5852_);
lean_dec(v_a_5851_);
lean_dec_ref(v_a_5850_);
lean_dec(v_a_5849_);
lean_dec_ref(v_a_5848_);
lean_dec_ref(v_ps_5845_);
return v_res_5858_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
